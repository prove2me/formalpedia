-- Prove2me | Theorems.Thm_UnderstandingML_sgd_learns_convex_lipschitz
-- name    : UnderstandingML.sgd_learns_convex_lipschitz
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T04:27:42.039584+00:00
-- url     : https://prove2.me/theorems/524a65d3-aee3-4560-a481-1a238220d50e
-- title:
--   Corollary 14.12: for a convex-Lipschitz-bounded problem (ρ, B), SGD on the risk with T ≥ B²ρ²/ε² examples and η = B/(ρ√T) has E[L_D(w̄)] ≤ min_{w∈H} L_D(w) + ε
-- statement:
--   **Corollary 14.12.** Consider a convex-Lipschitz-bounded learning problem with parameters $\rho, B$. Then, for every $\epsilon > 0$, if we run the SGD method for minimizing $L_D(w)$ with a number of iterations (i.e., number of examples) $T \ge B^2\rho^2/\epsilon^2$ and with $\eta = \sqrt{B^2/(\rho^2 T)}$, then the output of SGD satisfies $\mathbb{E}[L_D(\bar w)] \le \min_{w \in H} L_D(w) + \epsilon$.
--
--   Formally: the directions are $v_t \in \partial\ell(\cdot, z_t)(w^{(t)})$ chosen by a measurable selector; the loss is measurable, nonnegative and bounded at the origin so that risks are genuine integrals; "$\min$" is "for every $w \in H$".
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §14.5.1 pp. 197-198, Corollary 14.12 (from Theorem 14.8 and (14.13))

import Definitions.Def_UnderstandingML_SGD

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- **Corollary 14.12** (pp. 197–198). Consider a convex-Lipschitz-bounded learning problem with
parameters `ρ, B`. Then for every `ε > 0`, if we run the SGD method for minimizing `L_D(w)`,
with `vₜ ∈ ∂ℓ(w⁽ᵗ⁾, zₜ)` for fresh examples `zₜ ∼ D`, with a number of iterations (examples)
`T ≥ B²ρ²/ε²` and `η = √(B²/(ρ²T))`, then the output satisfies
`E[L_D(w̄)] ≤ min_{w ∈ H} L_D(w) + ε`. Stated for a measurable subgradient selector `g` and a
measurable, nonnegative loss bounded at the origin (so that risks are genuine integrals). -/
theorem sgd_learns_convex_lipschitz {d : ℕ} {Z : Type*} [MeasurableSpace Z] (H : Set (Vec d))
    (loss : Vec d → Z → ℝ) {ρ B : ℝ} (hρ : 0 < ρ) (hB : 0 < B)
    (hprob : ConvexLipschitzBounded H loss ρ B) (hmeas : Measurable (Function.uncurry loss))
    (hnonneg : ∀ w z, 0 ≤ loss w z) {C : ℝ} (hC : ∀ z, loss 0 z ≤ C) (g : Vec d → Z → Vec d)
    (hg : Measurable (Function.uncurry g)) (hsel : IsLossSubgradientSelector loss g) (ε : ℝ)
    (hε : 0 < ε) (T : ℕ) (hT : B ^ 2 * ρ ^ 2 / ε ^ 2 ≤ T) (D : Measure Z)
    [IsProbabilityMeasure D] :
    ∀ w ∈ H, ∫ S, risk loss D (sgdAverage (B / (ρ * Real.sqrt T)) g S) ∂(iidLaw D T) ≤
      risk loss D w + ε := by sorry

end UnderstandingML
