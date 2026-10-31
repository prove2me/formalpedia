-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P49_compact_directed_minimax
-- name    : QAlgorithms.Papers.Independent.Intake100.P49.compact_directed_minimax
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:29:42.746205+00:00
-- url     : https://prove2.me/theorems/1db7fb6c-6344-49f9-a311-f3aad01c22a0
-- title:
--   Compact-directed extended minimax with attained maxima
-- statement:
--   Let $X$ be a nonempty compact topological space, $Y$ a nonempty upward-directed partially ordered set, and $f:X\times Y\to[-\infty,+\infty]$.
--
--   For upper semicontinuous sections $f(\cdot,y)$ and antitone sections $f(x,\cdot)$, one has $$\max_{x\in X}\inf_{y\in Y}f(x,y)=\inf_{y\in Y}\max_{x\in X}f(x,y).$$ Each maximum on the right, as well as the maximum on the left, is attained. This permits an exchange of a directed infimum with a compact maximum.
-- source:
--   The strong converse exponent of discriminating infinite-dimensional quantum states, arXiv:2107.08036v5, PDF p. 4, Lemma II.5

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P49

noncomputable section

open Filter

open scoped ENNReal NNReal BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P49

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P13
  (IsPositive IsTraceClass TraceClass traceNormTopology)

open QAlgorithms.Papers.Independent.Bridge50.P48 (hilbertPositiveTrace)

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Lemma II.5, PDF p.4, (II.6): extended minimax and attainment of both suprema.
Nonempty X,Y are the source's implicit conventions for maxima and directedness. -/
theorem compact_directed_minimax {X Y : Type*} [TopologicalSpace X]
    [CompactSpace X] [Nonempty X] [PartialOrder Y] [Nonempty Y] [IsDirectedOrder Y]
    (f : X → Y → EReal)
    (husc : ∀ y, UpperSemicontinuous (fun x => f x y)) (hanti : ∀ x, Antitone (f x)) :
    (⨆ x, ⨅ y, f x y) = (⨅ y, ⨆ x, f x y) ∧
    (∀ y, ∃ x, f x y = ⨆ x, f x y) ∧
    (∃ x, (⨅ y, f x y) = ⨆ x, ⨅ y, f x y) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P49

end
