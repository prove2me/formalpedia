-- Prove2me | Theorems.Thm_PositivityTheory_Rg_BcB_CG_continuous_splitY_right
-- name    : PositivityTheory.Rg.BcB.CG.continuous_splitY_right
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:52:03.866277+00:00
-- url     : https://prove2.me/theorems/a144421e-e86f-4b5e-9434-b42e593bd48b
-- title:
--   CG: continuous split Y right
-- statement:
--   The CG construction uses the continuous split Y right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/HeckeFubiniCompatibility/PActPi.lean#L53-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/HeckeFubiniCompatibility/PActPi.lean#L53-L58

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_HeckeFubiniCompatibility_PActPi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.CG
variable {ι : Type} [DecidableEq ι] {X : Type}

theorem PositivityTheory.Rg.BcB.CG.continuous_splitY_right [TopologicalSpace X] (w : ι) (t : X) :
    Continuous fun z : {v // v ≠ w} → X => splitY w t z := by sorry
