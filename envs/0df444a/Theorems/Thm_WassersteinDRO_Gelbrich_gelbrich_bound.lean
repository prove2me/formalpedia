-- Prove2me | Theorems.Thm_WassersteinDRO_Gelbrich_gelbrich_bound
-- name    : WassersteinDRO.Gelbrich.gelbrich_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-21T02:27:34.057043+00:00
-- url     : https://prove2.me/theorems/08f2bad6-f179-4c4b-a3db-f647a27e1b28
-- title:
--   Theorem 4 — Gelbrich bound
-- statement:
--   If $\|\cdot\|$ is the Euclidean norm and the distributions $Q,Q'$ have mean vectors
--   $\mu,\mu' \in \mathbb{R}^m$ and covariance matrices $\Sigma,\Sigma' \in S^m_+$, then
--   $W_2(Q,Q') \ge \left(\|\mu-\mu'\|_2^2 + \mathrm{Tr}[\Sigma+\Sigma'-2(\Sigma^{1/2}\Sigma'\Sigma^{1/2})^{1/2}]\right)^{1/2}$,
--   with equality when $Q$ and $Q'$ are elliptical distributions with the same density generator $g$.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen & Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization, INFORMS TutORials 2019, Theorem 4, p. 8, eq. (8)

import Mathlib
import Definitions.Def_WassersteinDRO_Gelbrich_wassersteinDistance
import Definitions.Def_WassersteinDRO_Gelbrich_meanVector
import Definitions.Def_WassersteinDRO_Gelbrich_covarianceMatrix
import Definitions.Def_WassersteinDRO_Gelbrich_psdSqrt
import Definitions.Def_WassersteinDRO_Gelbrich_IsElliptical

open MeasureTheory

namespace WassersteinDRO.Gelbrich

/-- Theorem 4 (Gelbrich bound), Kuhn et al. 2019, p. 8, eq. (8): if `Q, Q'` have mean vectors
`μ, μ'` and covariance matrices `S, S' ∈ S^m_+`, then
`W2(Q,Q') ≥ (‖μ-μ'‖² + Tr[S+S'-2(S^{1/2}S'S^{1/2})^{1/2}])^{1/2}`, with equality if `Q, Q'`
are elliptical distributions with the same density generator `g`. -/
theorem gelbrich_bound {m : ℕ} (Q Q' : Measure (EuclideanSpace ℝ (Fin m)))
    (μ μ' : EuclideanSpace ℝ (Fin m)) (S S' : Matrix (Fin m) (Fin m) ℝ)
    (hS : S.PosSemidef) (hS' : S'.PosSemidef)
    (hμ : meanVector Q = μ) (hμ' : meanVector Q' = μ')
    (hSeq : covarianceMatrix Q = S) (hS'eq : covarianceMatrix Q' = S') :
    wassersteinDistance 2 Q Q' ≥
      ENNReal.ofReal (Real.sqrt (‖μ - μ'‖ ^ 2 +
        (S + S' - (2 : ℝ) • psdSqrt (psdSqrt S * S' * psdSqrt S)).trace)) ∧
    (∀ g : ℝ → ℝ, IsElliptical Q g μ S → IsElliptical Q' g μ' S' →
      wassersteinDistance 2 Q Q' =
        ENNReal.ofReal (Real.sqrt (‖μ - μ'‖ ^ 2 +
          (S + S' - (2 : ℝ) • psdSqrt (psdSqrt S * S' * psdSqrt S)).trace))) := by sorry

end WassersteinDRO.Gelbrich
