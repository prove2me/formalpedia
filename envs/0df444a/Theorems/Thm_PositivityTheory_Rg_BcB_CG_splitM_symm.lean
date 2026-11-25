-- Prove2me | Theorems.Thm_PositivityTheory_Rg_BcB_CG_splitM_symm
-- name    : PositivityTheory.Rg.BcB.CG.splitM_symm
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:51:57.159605+00:00
-- url     : https://prove2.me/theorems/cd644b46-909d-51ba-b392-5747bdf123e8
-- title:
--   CG: split M symm
-- statement:
--   The CG construction uses the split M symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/HeckeFubiniCompatibility/PActPi.lean#L105-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/HeckeFubiniCompatibility/PActPi.lean#L105-L110

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

theorem PositivityTheory.Rg.BcB.CG.splitM_symm [MeasurableSpace X] (w : ι) (t : X) (z : {v // v ≠ w} → X) :
    (splitM w).symm (t, z) = splitY w t z := by sorry
