-- Prove2me | Theorems.Thm_RollingProbeQN_Convex_lemma_D_8
-- name    : RollingProbeQN.Convex.lemma_D_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:21:43.90006+00:00
-- url     : https://prove2.me/theorems/337b8ed2-20be-4813-b090-46c429ac010d
-- title:
--   Lemma D.8 — the A-HPE iterates stay within $C_xR$ of a minimizer
-- statement:
--   Under the assumptions of Lemma D.1, for every $k\le N$,
--
--   $$\|x_k-x^\star\|\le C_xR,\qquad C_x=1+\frac{\sigma}{\sqrt{1-\sigma^2}},\qquad\text{hence}\qquad \zeta_k=\|z_k-x_k\|\le(1+C_x)R .$$
--
--   The constant depends only on $\sigma$: no dependence on $N$, $\varepsilon$, $d$ or a logarithm. It bounds the displacement $m_k$ in Appendix E.
--
--   Differences from the source:
--   - encoding: the recursion runs for k = 0, 1, … and the claim is for every k ≥ 0 → an A-HPE run up to an arbitrary horizon N, the claim for k < N (resp. k ≤ N); reason: N is arbitrary, so every finite stretch of an infinite run is covered; same instances
-- source:
--   Mokhtari, Patitucci, Improved Gradient Complexity for Quasi-Newton Proximal Extragradient Methods via Certified Curvature Reuse, arXiv:2610.40608, Lemma D.8, p. 39

import Mathlib
import Definitions.Def_RollingProbeQN_Convex_IsAHPERun
import Definitions.Def_RollingProbeQN_Convex_Cx

namespace RollingProbeQN.Convex

/-- **Lemma D.8 (Boundedness of the iterates).**
Mokhtari, Patitucci, *Improved Gradient Complexity for Quasi-Newton Proximal Extragradient
Methods via Certified Curvature Reuse*, arXiv:2610.40608, Lemma D.8, p. 39: "For all `k ≥ 0`, `‖x_k − x★‖ ≤ C_x R`, `C_x := 1 + σ/√(1 − σ²)`, hence
`ζ_k = ‖z_k − x_k‖ ≤ (1 + C_x)R`."

**Formalization Note.** Standing assumptions of Appendix D.1 as in `lemma_D_1`; the run has horizon
`N` and the bounds hold for every `k ≤ N`. -/
theorem lemma_D_8 {d : ℕ} {F : EuclideanSpace ℝ (Fin d) → ℝ} {σ R : ℝ} {N : ℕ} {lam : ℕ → ℝ}
    {x y z : ℕ → EuclideanSpace ℝ (Fin d)} {A : ℕ → ℝ} {xstar : EuclideanSpace ℝ (Fin d)}
    (hconv : ConvexOn ℝ Set.univ F) (hdiff : Differentiable ℝ F)
    (hmin : IsMinOn F Set.univ xstar) (hσ0 : 0 < σ) (hσ1 : σ < 1) (hR : ‖x 0 - xstar‖ ≤ R)
    (hrun : IsAHPERun F σ N lam x y z A) :
    ∀ k ≤ N, ‖x k - xstar‖ ≤ Cx σ * R ∧ ‖z k - x k‖ ≤ (1 + Cx σ) * R := by sorry

end RollingProbeQN.Convex
