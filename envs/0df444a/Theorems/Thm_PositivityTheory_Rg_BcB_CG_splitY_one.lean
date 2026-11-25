-- Prove2me | Theorems.Thm_PositivityTheory_Rg_BcB_CG_splitY_one
-- name    : PositivityTheory.Rg.BcB.CG.splitY_one
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:52:10.895287+00:00
-- url     : https://prove2.me/theorems/06bd7f4b-5b36-43cc-af01-97e4304127e1
-- title:
--   CG: split Y one
-- statement:
--   The CG construction uses the split Y one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/HeckeFubiniCompatibility/PActPi.lean#L42-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/HeckeFubiniCompatibility/PActPi.lean#L42-L44

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

theorem PositivityTheory.Rg.BcB.CG.splitY_one [One X] (w : ι) : splitY w (1 : X) (1 : {v // v ≠ w} → X) = 1 := by sorry
