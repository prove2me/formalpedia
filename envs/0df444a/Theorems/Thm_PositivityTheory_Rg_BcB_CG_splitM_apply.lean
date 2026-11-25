-- Prove2me | Theorems.Thm_PositivityTheory_Rg_BcB_CG_splitM_apply
-- name    : PositivityTheory.Rg.BcB.CG.splitM_apply
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:52:06.116742+00:00
-- url     : https://prove2.me/theorems/a070c881-decd-49c9-95ca-9c893ceecba1
-- title:
--   CG: split M apply
-- statement:
--   The CG construction uses the split M apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/HeckeFubiniCompatibility/PActPi.lean#L103-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/HeckeFubiniCompatibility/PActPi.lean#L103-L103

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
variable {Idx : ι → Type}

theorem PositivityTheory.Rg.BcB.CG.splitM_apply [MeasurableSpace X] (w : ι) (y : ι → X) : splitM w y = (y w, fun v : {v // v ≠ w} => y v) := by sorry
