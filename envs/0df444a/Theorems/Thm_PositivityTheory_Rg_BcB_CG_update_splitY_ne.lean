-- Prove2me | Theorems.Thm_PositivityTheory_Rg_BcB_CG_update_splitY_ne
-- name    : PositivityTheory.Rg.BcB.CG.update_splitY_ne
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:52:22.55705+00:00
-- url     : https://prove2.me/theorems/d24e1c46-b1e0-45cf-93ea-83f7ab201378
-- title:
--   CG: update split Y ne
-- statement:
--   The CG construction uses the update split Y ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/HeckeFubiniCompatibility/PActPi.lean#L28-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/HeckeFubiniCompatibility/PActPi.lean#L28-L40

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

theorem PositivityTheory.Rg.BcB.CG.update_splitY_ne (w : ι) (t : X) (z : {v // v ≠ w} → X) (v : {v // v ≠ w}) (s : X) :
    Function.update (splitY w t z) v s = splitY w t (Function.update z v s) := by sorry
