-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P42_slowMetric_firstJet
-- name    : QAlgorithms.Papers.Independent.Renew46.P42.slowMetric_firstJet
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T21:28:54.51454+00:00
-- url     : https://prove2.me/theorems/03555280-79fe-497f-a5ad-51a58273017d
-- title:
--   First-order metric and kinetic/canonical momentum
-- statement:
--   In the nondispersive optical model take $c>0$, $n\ge1$, $\mathbf k\ne0$ and fixed $\mathbf u,\omega$. Equality $\sim_1$ denotes equality of values and derivatives at $\epsilon=0$. For flow $\epsilon\mathbf u$, the covariant and contravariant Gordon metrics have first jets
--
--   $$g\sim_1\begin{pmatrix}n^{-2}&(n^2-1)\epsilon\mathbf u^T/(n^2c)\\(n^2-1)\epsilon\mathbf u/(n^2c)&-I\end{pmatrix},\qquad G\sim_1\begin{pmatrix}n^2&(n^2-1)\epsilon\mathbf u^T/c\\(n^2-1)\epsilon\mathbf u/c&-I\end{pmatrix}.$$
--
--   Raising $(\omega/c,-\mathbf k)$ gives spatial momentum
--
--   $$\mathbf K\sim_1\mathbf k+(n^2-1)\omega\epsilon\mathbf u/c^2.$$
--
--   When $\omega=H_\epsilon$, this also equals $(n/c)\mathbf w_\epsilon$ through first order, where $\mathbf w_\epsilon=|\mathbf k|\partial_{\mathbf k}H_\epsilon$.
--
--   These formulas identify the raised momentum with kinetic momentum in the retained model.
-- source:
--   Optics of Nonuniformly Moving Media, arXiv:physics/9906038v3, PDF p. 6, §III E, (58)–(61): first-order metric and kinetic/canonical momentum

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P42

namespace QAlgorithms.Papers.Independent.Renew46.P42

noncomputable section

open scoped BigOperators

open Filter Set MeasureTheory

-- Reuse the pinned accepted real quadratic form (arbitrary finite real matrices).

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

/-- PDF pp.6–7, (58)–(61): metric first jets and kinetic/canonical momentum.
Source correction: printed (61) has omega/c; (13),(29),(55) require omega/c^2. -/
theorem slowMetric_firstJet (c n omega : ℝ) (u k : V3)
    (hc : 0 < c) (hn : 1 ≤ n) (hk : k ≠ 0) :
    (∀ i j : Fin 4,
      FirstJetEq (fun eps => gDown c n (eps • u) i j)
        (fun eps => slowDown c n (eps • u) i j)) ∧
    (∀ i j : Fin 4,
      FirstJetEq (fun eps => gUp c n (eps • u) i j)
        (fun eps => slowUp c n (eps • u) i j)) ∧
    FirstJetEq (fun eps => spatial (apply4 (gUp c n (eps • u)) (waveCovector c omega k)))
      (fun eps => k + ((n ^ 2 - 1) * omega / c ^ 2) • (eps • u)) ∧
    FirstJetEq (fun eps => spatial (apply4 (gUp c n (eps • u))
        (waveCovector c (rayHamiltonian c n (eps • u) k) k)))
      (fun eps => (n / c) • modifiedVelocity c n (eps • u) k) := by sorry

end

end QAlgorithms.Papers.Independent.Renew46.P42
