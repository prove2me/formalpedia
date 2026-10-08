-- Prove2me | Theorems.Thm_WassersteinDRO_Gelbrich_gelbrich_risk_bound
-- name    : WassersteinDRO.Gelbrich.gelbrich_risk_bound
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-21T02:29:26.256374+00:00
-- url     : https://prove2.me/theorems/5a756296-a7e8-40b2-bdcb-82a39eff2ef2
-- title:
--   Corollary 1 — Gelbrich risk bound
-- statement:
--   If the nominal distribution $\hat P_N$ has mean vector $\hat\mu$ and covariance matrix
--   $\hat\Sigma$ and $p \ge 2$, then for every loss function $\ell$ the worst-case risk over the
--   Wasserstein ambiguity set is bounded above by the Gelbrich risk:
--   $R_{\varepsilon,p}(\hat P_N,\ell) \le R_\varepsilon(\hat\mu,\hat\Sigma,\ell)$.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen & Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization, INFORMS TutORials 2019, Corollary 1, p. 18, eq. (18)

import Mathlib
import Definitions.Def_WassersteinDRO_Gelbrich_worstCaseRisk
import Definitions.Def_WassersteinDRO_Gelbrich_gelbrichRisk

open MeasureTheory

namespace WassersteinDRO.Gelbrich

/-- Corollary 1 (Gelbrich risk), Kuhn et al. 2019, p. 18, eq. (18): if `P̂N` has mean vector
`μ̂` and covariance matrix `Ŝ` and `p ≥ 2`, then the worst-case risk of any fixed loss
function `ℓ` is bounded above by the Gelbrich risk, `R_{ε,p}(P̂N,ℓ) ≤ R_ε(μ̂,Ŝ,ℓ)`. (The
paper's companion statement for the worst-case *optimal* risk over a loss class `L`,
`R_{ε,p}(P̂N,L) ≤ R_ε(μ̂,Ŝ,L)`, follows immediately by taking the infimum over `ℓ ∈ L` on both
sides of this bound and is not separately formalized — see `STATUS.md`.) -/
theorem gelbrich_risk_bound {m : ℕ} (ε p : ℝ) (hp : 2 ≤ p) (Ξ : Set (EuclideanSpace ℝ (Fin m)))
    (PN : Measure (EuclideanSpace ℝ (Fin m))) (μhat : EuclideanSpace ℝ (Fin m))
    (SigmaHat : Matrix (Fin m) (Fin m) ℝ) (hμ : meanVector PN = μhat) (hS : covarianceMatrix PN = SigmaHat)
    (ℓ : EuclideanSpace ℝ (Fin m) → ℝ) :
    worstCaseRisk ε p Ξ PN ℓ ≤ gelbrichRisk ε Ξ μhat SigmaHat ℓ := by sorry

end WassersteinDRO.Gelbrich
