-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P12_theorem_8_1
-- name    : QAlgorithms.Papers.Independent.Support50.P12.theorem_8_1
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:51:56.171982+00:00
-- url     : https://prove2.me/theorems/803f2018-d171-4151-be73-24d7fa41435f
-- title:
--   Theorem 8.1
-- statement:
--   Let $f:[0,\infty)\to\mathbb R$ be continuous, including at zero. Operator convexity is tested on all positive semidefinite finite matrices.
--
--   The function is operator convex exactly when there exist $a\in\mathbb R$, $b\ge0$, and a positive measure $\mu$ on $(0,\infty)$ with $\int(1+t)^{-2}\,d\mu(t)<\infty$ such that
--
--   $$f(x)=f(0)+ax+bx^2+\int_{(0,\infty)}\left(\frac{x}{1+t}-\frac{x}{x+t}\right)d\mu(t),\qquad x\ge0.$$
--
--   All three parameters are unique, $b=\lim_{x\to\infty}f(x)/x^2$, and $a=f(1)-f(0)-b$. Integrability is asserted for the combined kernel. This is the representation used in the equality criteria.
-- source:
--   Quantum f-divergences and error correction, arXiv:1008.2529v6, PDF p. 37, Theorem 8.1

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

/-- Theorem 8.1, PDF pp.37–38: iff, uniqueness of ALL parameters, and both
parameter formulas. Continuity includes zero; kernels are never split into divergent integrals. -/
theorem theorem_8_1 (f : ℝ → ℝ) (hf : ContinuousOn f (Ici 0)) :
    (SemidefiniteOperatorConvex f ↔ ∃ (a b : ℝ) (mu : Measure PosReal), HalfLineRepresentation f a b mu) ∧
    (∀ (a b a2 b2 : ℝ) (mu nu : Measure PosReal), HalfLineRepresentation f a b mu →
      HalfLineRepresentation f a2 b2 nu → a = a2 ∧ b = b2 ∧ mu = nu) ∧
    (∀ (a b : ℝ) (mu : Measure PosReal), HalfLineRepresentation f a b mu →
      Tendsto (fun x : ℝ => f x / x ^ 2) atTop (𝓝 b) ∧ a = f 1 - f 0 - b) := by sorry

end QAlgorithms.Papers.Independent.Support50.P12

end
