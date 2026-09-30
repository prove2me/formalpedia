-- Prove2me | Theorems.Thm_UnderstandingML_sgd_strongly_convex
-- name    : UnderstandingML.sgd_strongly_convex
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T04:26:48.312982+00:00
-- url     : https://prove2.me/theorems/3a08d4a2-b92d-4a66-9410-baa83254be71
-- title:
--   Theorem 14.11: for λ-strongly convex f, E‖vₜ‖² ≤ ρ² and w⋆ ∈ H, SGD with ηₜ = 1/(λt) and projections onto H has E[f(w̄)] − f(w⋆) ≤ (ρ²/(2λT))(1 + log T)
-- statement:
--   **Theorem 14.11.** Assume that $f$ is $\lambda$-strongly convex and that $\mathbb{E}[\|v_t\|^2] \le \rho^2$. Let $w^\star \in \operatorname{argmin}_{w \in H} f(w)$ be an optimal solution. Then SGD with $\eta_t = 1/(\lambda t)$ and a projection onto $H$ after each step satisfies
--   $$\mathbb{E}[f(\bar w)] - f(w^\star) \le \frac{\rho^2}{2\lambda T}(1 + \log T).$$
--
--   Formally: $H$ closed and convex, directions $v_t = g(w^{(t)}, z_t)$ for i.i.d. $z_t \sim D$ and a measurable oracle with $\mathbb{E}_z g(w,z) \in \partial f(w)$ and $\mathbb{E}_z\|g(w,z)\|^2 \le \rho^2$ for every $w$; the bound holds for every $w^\star \in H$.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §14.4.4 pp. 195-196, Theorem 14.11 with its proof

import Definitions.Def_UnderstandingML_SGD

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- **Theorem 14.11** (p. 195). Assume that `f` is `λ`-strongly convex and that `E[‖vₜ‖²] ≤ ρ²`.
Let `w⋆ ∈ argmin_{w ∈ H} f(w)` (the bound holds for every `w⋆ ∈ H`). Then SGD with the step
sizes `ηₜ = 1/(λt)` and a projection onto the closed convex set `H` after each step satisfies
`E[f(w̄)] − f(w⋆) ≤ (ρ²/(2λT))(1 + log T)`. Directions `vₜ = g(w⁽ᵗ⁾, zₜ)` for i.i.d. `zₜ ∼ D`, an
oracle `g` with `E_z g(w, z) ∈ ∂f(w)` and `E_z ‖g(w, z)‖² ≤ ρ²` for every `w`. -/
theorem sgd_strongly_convex {d : ℕ} {Z : Type*} [MeasurableSpace Z] (f : Vec d → ℝ) {lam : ℝ}
    (hlam : 0 < lam) (hf : StrongConvexOn Set.univ lam f) (H : Set (Vec d)) (hH : Convex ℝ H)
    (hclosed : IsClosed H) (D : Measure Z) [IsProbabilityMeasure D] (g : Vec d → Z → Vec d)
    (hg : Measurable (Function.uncurry g)) (horacle : IsSubgradientOracle f D g) {ρ : ℝ}
    (hmoment : ∀ w, ∫⁻ z, ENNReal.ofReal (‖g w z‖ ^ 2) ∂D ≤ ENNReal.ofReal (ρ ^ 2))
    (wstar : Vec d) (hw : wstar ∈ H) (T : ℕ) (hT : 0 < T) :
    (∫ S, f (sgdStrongAverage lam H g S) ∂(iidLaw D T)) - f wstar ≤
      ρ ^ 2 / (2 * lam * T) * (1 + Real.log T) := by sorry

end UnderstandingML
