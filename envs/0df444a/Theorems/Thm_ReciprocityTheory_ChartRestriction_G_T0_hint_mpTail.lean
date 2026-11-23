-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_hint_mpTail
-- name    : ReciprocityTheory.ChartRestriction.G.T0.hint_mpTail
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:51:51.615938+00:00
-- url     : https://prove2.me/theorems/da7f8f08-91ff-49c2-a705-2100defda97e
-- title:
--   T0: hint mp Tail
-- statement:
--   The T0 construction uses the hint mp Tail property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HintIntOfBounds.lean#L33-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HintIntOfBounds.lean#L33-L51

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

theorem ReciprocityTheory.ChartRestriction.G.T0.hint_mpTail (D n : ℕ) (hn : 0 < n) :
    MeasurePreserving (fun z : BlockSphere (D + 1) n => fun i : Fin D => z i.succ)
      (blockSphereProb (D + 1) n) (blockSphereProb D n) := by sorry
