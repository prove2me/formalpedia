-- Prove2me | Theorems.Thm_UnderstandingML_sgd_convex_smooth
-- name    : UnderstandingML.sgd_convex_smooth
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T04:28:27.958784+00:00
-- url     : https://prove2.me/theorems/68460b22-87fe-4b16-80a0-747ed3ca5e70
-- title:
--   Theorem 14.13: for convex β-smooth nonnegative losses and ηβ < 1, SGD on the risk with gradient directions has E[L_D(w̄)] ≤ (1/(1 − ηβ))(L_D(w⋆) + ‖w⋆‖²/(2ηT))
-- statement:
--   **Theorem 14.13.** Assume that for all $z$, the loss function $\ell(\cdot, z)$ is convex, $\beta$-smooth, and nonnegative. Then, if we run the SGD algorithm for minimizing $L_D(w)$ we have that for every $w^\star$,
--   $$\mathbb{E}[L_D(\bar w)] \le \frac{1}{1 - \eta\beta}\Big(L_D(w^\star) + \frac{\|w^\star\|^2}{2\eta T}\Big).$$
--
--   Formally: directions $v_t = \nabla\ell(\cdot, z_t)(w^{(t)})$, $0 < \eta$, $\eta\beta < 1$, $T \ge 1$; the loss and its gradient map are measurable and the loss is bounded at the origin.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §14.5.2 pp. 198-199, Theorem 14.13 with its proof

import Definitions.Def_UnderstandingML_SGD

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- **Theorem 14.13** (p. 198). Assume that for all `z` the loss function `ℓ(·, z)` is convex,
`β`-smooth and nonnegative. Then running SGD for minimizing `L_D(w)` with the gradient directions
`vₜ = ∇ℓ(·, zₜ)(w⁽ᵗ⁾)`, a step size `η` with `ηβ < 1` and `T ≥ 1` steps gives, for every `w⋆`,
`E[L_D(w̄)] ≤ (1/(1 − ηβ)) (L_D(w⋆) + ‖w⋆‖²/(2ηT))`. Measurability of the loss and of its
gradient map, and a bound at the origin, so that all expectations are genuine. -/
theorem sgd_convex_smooth {d : ℕ} {Z : Type*} [MeasurableSpace Z] (loss : Vec d → Z → ℝ)
    (hconv : ∀ z, ConvexOn ℝ Set.univ (fun w ↦ loss w z)) (hnonneg : ∀ w z, 0 ≤ loss w z)
    {β : ℝ} (hβ : 0 ≤ β) (hsmooth : IsSmoothLoss β loss)
    (hmeas : Measurable (Function.uncurry loss))
    (hgrad : Measurable (Function.uncurry fun w z ↦ gradient (fun w ↦ loss w z) w)) {C : ℝ}
    (hC : ∀ z, loss 0 z ≤ C) {η : ℝ} (hη : 0 < η) (hηβ : η * β < 1) (T : ℕ) (hT : 0 < T)
    (D : Measure Z) [IsProbabilityMeasure D] (wstar : Vec d) :
    ∫ S, risk loss D (sgdAverage η (fun w z ↦ gradient (fun w ↦ loss w z) w) S) ∂(iidLaw D T) ≤
      1 / (1 - η * β) * (risk loss D wstar + ‖wstar‖ ^ 2 / (2 * η * T)) := by sorry

end UnderstandingML
