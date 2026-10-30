-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P10_monotone_parameter_minimax
-- name    : QAlgorithms.Papers.Independent.Advance50.P10.monotone_parameter_minimax
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:56:32.197507+00:00
-- url     : https://prove2.me/theorems/9d0ccaf6-e6b1-4800-9b8f-c89c61b12997
-- title:
--   Corollary A.2: monotone-parameter minimax
-- statement:
--   Let $X$ be a nonempty compact topological space, let $Y\subset\mathbb R$ be nonempty, and let $f:X\times Y\to\overline{\mathbb R}$. Suppose each $f(\cdot,y)$ is lower semicontinuous. Assume either that every $f(x,\cdot)$ is nondecreasing, or that every $f(x,\cdot)$ is nonincreasing, with one common choice of direction. Then
--
--   $$\sup_{y\in Y}\min_{x\in X}f(x,y)=\min_{x\in X}\sup_{y\in Y}f(x,y).$$
--
--   Each fixed-$y$ infimum and the infimum of the pointwise supremum is attained. No separation axiom on $X$ is required. This is the parameter-monotone form of the extended minimax theorem.
-- source:
--   On the quantum Renyi relative entropies and related capacity formulas, arXiv:0912.1286v4, PDF p. 11, Corollary A.2: monotone-parameter minimax

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P10

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate ENNReal Topology

open Filter Set MeasureTheory

namespace QAlgorithms.Papers.Independent.Advance50.P10

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P58 (Operator)

open QAlgorithms.Papers.Independent.Information100.P60 (copies)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart)

open QAlgorithms.Papers.Independent.Dependency50.P18 (logBits)

open QAlgorithms.Papers.Independent.Dependency50.P25 (extendedIntegral)

open QAlgorithms.Papers.Independent.Dependency50.P35 (maxRelative)

open QAlgorithms.Papers.Independent.Bridge50.P45 (tensorEntries lifted comparison)

-- Density subtypes below reuse the frozen PSD/trace-one predicate directly.

-- The source uses Borel laws, with the weak topology on probability measures.

attribute [local instance] QAlgorithms.Papers.Independent.Advance50.P10.densityMeasurableSpace

attribute [local instance] QAlgorithms.Papers.Independent.Advance50.P10.densityBorelSpace

/-- Corollary A.2, PDF p.11: a common monotonicity direction for all x.
The order codomain is the extended real line, as confirmed from the original PDF. -/
theorem monotone_parameter_minimax {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [Nonempty X] (Y : Set ℝ) (hY : Y.Nonempty) (f : X → Y → EReal)
    (hlsc : ∀ y, LowerSemicontinuous (fun x => f x y))
    (hmonotone : (∀ x, Monotone (f x)) ∨ (∀ x, Antitone (f x))) :
    (∀ y, ReachesMinimum (fun x => f x y)) ∧
    ReachesMinimum (fun x => ⨆ y, f x y) ∧
    (⨆ y, ⨅ x, f x y) = (⨅ x, ⨆ y, f x y) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P10

end
