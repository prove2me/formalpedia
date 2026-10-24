-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P12_proposition_8_4
-- name    : QAlgorithms.Papers.Independent.Support50.P12.proposition_8_4
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:54:09.445284+00:00
-- url     : https://prove2.me/theorems/69e73619-c01b-4c66-bea5-749747cbfbdf
-- title:
--   Proposition 8.4
-- statement:
--   Let $f:[0,\infty)\to\mathbb R$ be continuous, including at zero.
--
--   Operator convexity with a finite real recession slope is equivalent to the existence of $a\in\mathbb R$ and a positive measure $\mu$ with $\int(1+t)^{-1}d\mu(t)<\infty$ such that
--
--   $$f(x)=f(0)+ax-\int_{(0,\infty)}\frac{x}{x+t}\,d\mu(t),\qquad x\ge0.$$
--
--   The coefficient $a$ need not be positive. The stronger weight condition makes each displayed separated integral integrable.
-- source:
--   Quantum f-divergences and error correction, arXiv:1008.2529v6, PDF p. 40, Proposition 8.4

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

/-- Proposition 8.4, PDF pp.40–41: finite REAL slope, with no positivity restriction
on alpha, and the stronger integrable weight allowing the separated formula. -/
theorem proposition_8_4 (f : ℝ → ℝ) (hf : ContinuousOn f (Ici 0)) :
    (SemidefiniteOperatorConvex f ∧ ∃ a : ℝ, Tendsto (fun x : ℝ => f x / x) atTop (𝓝 a)) ↔
      ∃ (a : ℝ) (mu : Measure PosReal),
        Integrable (fun t : PosReal => 1 / (1 + t.1)) mu ∧
        ∀ x ≥ 0, Integrable (fun t : PosReal => x / (x + t.1)) mu ∧
          f x = f 0 + a * x - ∫ t, x / (x + t.1) ∂mu := by sorry

end QAlgorithms.Papers.Independent.Support50.P12

end
