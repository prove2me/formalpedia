-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_hint_mpSplit
-- name    : ReciprocityTheory.ChartRestriction.G.T0.hint_mpSplit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:16:40.343418+00:00
-- url     : https://prove2.me/theorems/8aed6d29-5e3a-40fc-b5ec-22d8471fbde9
-- title:
--   T0: hint mp Split
-- statement:
--   The T0 construction uses the hint mp Split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HintIntOfBounds.lean#L15-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HintIntOfBounds.lean#L15-L19

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
import Definitions.Def_ReciprocityTheory_SemistableReduction_RestBlockSubstIsMultiHomogeneous
import Definitions.Def_ReciprocityTheory_SemistableReduction_IntCoresA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HintIntOfBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open MeasureTheory ReciprocityTheory.MultiplicativeHeights

theorem ReciprocityTheory.ChartRestriction.G.T0.hint_mpSplit (D n : ℕ) (hn : 0 < n) :
    MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (D + 1) => UnitSphereC n) 0)
      (blockSphereProb (D + 1) n) ((sphereProb n).prod (blockSphereProb D n)) := by sorry
