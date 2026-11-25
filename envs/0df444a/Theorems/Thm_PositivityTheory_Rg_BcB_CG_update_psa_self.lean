-- Prove2me | Theorems.Thm_PositivityTheory_Rg_BcB_CG_update_psa_self
-- name    : PositivityTheory.Rg.BcB.CG.update_psa_self
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:52:08.771277+00:00
-- url     : https://prove2.me/theorems/e39a039c-4719-515d-b75f-34d0772e9274
-- title:
--   CG: update psa self
-- statement:
--   The CG construction uses the update psa self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/HeckeFubiniCompatibility/PActPi.lean#L75-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/HeckeFubiniCompatibility/PActPi.lean#L75-L83

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

theorem PositivityTheory.Rg.BcB.CG.update_psa_self (w : ι) (j j' : Idx w) (J' : ∀ v : {v // v ≠ w}, Idx v) :
    Function.update ((Equiv.piSplitAt w Idx).symm (j, J')) w j' = (Equiv.piSplitAt w Idx).symm (j', J') := by sorry
