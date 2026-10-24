-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P12_corollary_8_2
-- name    : QAlgorithms.Papers.Independent.Support50.P12.corollary_8_2
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:52:38.976172+00:00
-- url     : https://prove2.me/theorems/779924db-654a-4a02-a37b-4dea17fc1489
-- title:
--   Corollary 8.2
-- statement:
--   Let $f$ be continuous and operator convex on $[0,\infty)$ and not the restriction of a real polynomial. Then $f$ is differentiable at one.
--
--   There exist $b=\lim_{x\to\infty}f(x)/x^2\ge0$ and a positive measure $\mu$ such that
--
--   $$f(x)=f(0)+bx^2+\int_{(0,\infty)}\left(\eta(t)x-\frac{x}{x+t}\right)d\mu(t),$$
--
--   $$\eta(t)=\frac1{1+t}+\frac{f(1)-f(0)-b}{f\prime(1)-f(1)+f(0)-b}\frac1{(1+t)^2}.$$
--
--   The denominator is strictly positive as a conclusion, not a hypothesis. If $b=0$ and $f\prime(1)\ge0$, then $\eta(t)\ge0$ for every $t>0$. The combined integrand is integrable; the linear term need not be separately integrable.
-- source:
--   Quantum f-divergences and error correction, arXiv:1008.2529v6, PDF p. 39, Corollary 8.2

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P12

noncomputable section

namespace QAlgorithms.Papers.Independent.Support50.P12

open Filter MeasureTheory Set

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap)

open QAlgorithms.Papers.Independent.Dependency50.P28 (tr LE logNonnegativeExtended pinch)

open QAlgorithms.Papers.Independent.Dependency50.P21 (channelAdjoint spectralFunction petz relativeEntropy)

open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

open QAlgorithms.Papers.Independent.Next46.P23 (Supports)

open QAlgorithms.Papers.Independent.Support21.P03 (ExtendedConvex)

open QAlgorithms (spectralProjector)

open QAlgorithms.Learning (IsDistribution)

open QAlgorithms.Papers.Independent.Information100.P04 (absOp)

open scoped BigOperators Matrix ComplexConjugate ComplexOrder ENNReal Topology Kronecker

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

variable {I J K : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype K] [DecidableEq K]

/-- Corollary 8.2, PDF p.39: the explicit psi, including its DERIVED strictly
positive denominator, and the b=0, f'(1)>=0 positivity refinement. -/
theorem corollary_8_2 (f : ℝ → ℝ) (hf : ContinuousOn f (Ici 0)) (ho : SemidefiniteOperatorConvex f)
    (hn : ¬ ∃ P : Polynomial ℝ, ∀ x ≥ 0, f x = P.eval x) :
    DifferentiableAt ℝ f 1 ∧ ∃ (b : ℝ) (mu : Measure PosReal),
      0 ≤ b ∧ Tendsto (fun x : ℝ => f x / x ^ 2) atTop (𝓝 b) ∧
      0 < deriv f 1 - f 1 + f 0 - b ∧
      let q : PosReal → ℝ := fun t => 1 / (1 + t.1) +
        (f 1 - f 0 - b) / (deriv f 1 - f 1 + f 0 - b) * (1 / (1 + t.1) ^ 2)
      (∀ x ≥ 0, Integrable (fun t => q t * x - x / (x + t.1)) mu ∧
        f x = f 0 + b * x ^ 2 + ∫ t, (q t * x - x / (x + t.1)) ∂mu) ∧
      (b = 0 → 0 ≤ deriv f 1 → ∀ t, 0 ≤ q t) := by sorry

end QAlgorithms.Papers.Independent.Support50.P12

end
