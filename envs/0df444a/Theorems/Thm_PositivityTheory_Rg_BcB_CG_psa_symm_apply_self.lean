-- Prove2me | Theorems.Thm_PositivityTheory_Rg_BcB_CG_psa_symm_apply_self
-- name    : PositivityTheory.Rg.BcB.CG.psa_symm_apply_self
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:52:05.758836+00:00
-- url     : https://prove2.me/theorems/5ec64515-e1ac-47b5-a0dd-d577f0d4fbb7
-- title:
--   CG: psa symm apply self
-- statement:
--   The CG construction uses the psa symm apply self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/HeckeFubiniCompatibility/PActPi.lean#L72-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/HeckeFubiniCompatibility/PActPi.lean#L72-L73

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

theorem PositivityTheory.Rg.BcB.CG.psa_symm_apply_self (w : ι) (J : ∀ v, Idx v) : (Equiv.piSplitAt w Idx).symm (J w, fun v : {v // v ≠ w} => J v) = J := by sorry
