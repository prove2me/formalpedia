-- Prove2me | Theorems.Thm_PositivityTheory_Rg_BcB_CG_continuous_splitY_left
-- name    : PositivityTheory.Rg.BcB.CG.continuous_splitY_left
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:51:52.304694+00:00
-- url     : https://prove2.me/theorems/e5de4df5-ee87-4ef8-a5b5-9356bf313668
-- title:
--   CG: continuous split Y left
-- statement:
--   The CG construction uses the continuous split Y left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/HeckeFubiniCompatibility/PActPi.lean#L46-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/HeckeFubiniCompatibility/PActPi.lean#L46-L51

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

theorem PositivityTheory.Rg.BcB.CG.continuous_splitY_left [TopologicalSpace X] (w : ι) (z : {v // v ≠ w} → X) :
    Continuous fun t : X => splitY w t z := by sorry
