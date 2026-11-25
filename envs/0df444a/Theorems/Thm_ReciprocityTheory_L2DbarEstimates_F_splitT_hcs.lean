-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_splitT_hcs
-- name    : ReciprocityTheory.L2DbarEstimates.F.splitT_hcs
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:58:09.234016+00:00
-- url     : https://prove2.me/theorems/172f090e-b830-5766-8053-bc9f0cf9b31a
-- title:
--   F: split T hcs
-- statement:
--   The F construction uses the split T hcs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/SplitTest.lean#L97-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/SplitTest.lean#L97-L100

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_MinimalSolutions_HilbertLemmas
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_SplitTest
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M] {n : ℕ} {z : M → V n}

theorem ReciprocityTheory.L2DbarEstimates.F.splitT_hcs {X : Type*} [Zero X] (u : M → X) (S : Fin n → Set M)
    (hS : ∀ j, IsCompact (S j)) (h : ∀ x, (∀ j, x ∉ S j) → u x = 0) : HasCompactSupport u := by sorry
