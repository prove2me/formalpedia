-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P10_extended_minimax_from_finite_subsets
-- name    : QAlgorithms.Papers.Independent.Advance50.P10.extended_minimax_from_finite_subsets
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:55:52.587791+00:00
-- url     : https://prove2.me/theorems/874a3cac-accd-488d-827c-c9ffcf91fe42
-- title:
--   Lemma A.1: extended minimax from finite subsets
-- statement:
--   Let $X$ be a nonempty compact topological space, $Y$ a nonempty set, and $f:X\times Y\to\overline{\mathbb R}$. No Hausdorff assumption is imposed. Suppose $f(\cdot,y)$ is lower semicontinuous for every $y$, and for every finite nonempty $Y^\prime\subset Y$,
--
--   $$\inf_{x\in X}\max_{y\in Y^\prime}f(x,y)\le\sup_{y\in Y}\inf_{x\in X}f(x,y).$$
--
--   Then every fixed-$y$ infimum and the infimum of $x\mapsto\sup_y f(x,y)$ are attained, and
--
--   $$\sup_{y\in Y}\min_{x\in X}f(x,y)=\min_{x\in X}\sup_{y\in Y}f(x,y).$$
--
--   All extrema use the extended real line. The empty finite subset can equivalently be included with supremum $-\infty$. This is the minimax step reproduced from Komiya’s proof.
-- source:
--   On the quantum Renyi relative entropies and related capacity formulas, arXiv:0912.1286v4, PDF p. 11, Lemma A.1: extended minimax from finite subsets

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

/-- Lemma A.1, PDF p.11: the extended minimax lemma reproduced from Komiya's proof.
All infima appearing in (39), including each fixed-y infimum, actually attain minima.
No separation axiom on X is assumed. -/
theorem extended_minimax_from_finite_subsets {X Y : Type*} [TopologicalSpace X]
    [CompactSpace X] [Nonempty X] [Nonempty Y] (f : X → Y → EReal)
    (hlsc : ∀ y, LowerSemicontinuous (fun x => f x y))
    (hfinite : ∀ s : Finset Y,
      (⨅ x, ⨆ y : {y // y ∈ s}, f x y.1) ≤ ⨆ y, ⨅ x, f x y) :
    (∀ y, ReachesMinimum (fun x => f x y)) ∧
    ReachesMinimum (fun x => ⨆ y, f x y) ∧
    (⨆ y, ⨅ x, f x y) = (⨅ x, ⨆ y, f x y) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P10

end
