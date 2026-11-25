-- Prove2me | Theorems.Thm_PositivityTheory_Rg_BcB_CG_update_psa_ne
-- name    : PositivityTheory.Rg.BcB.CG.update_psa_ne
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:52:00.917975+00:00
-- url     : https://prove2.me/theorems/6529ff79-387b-55f7-8e6b-eed7207ddc1e
-- title:
--   CG: update psa ne
-- statement:
--   The CG construction uses the update psa ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/HeckeFubiniCompatibility/PActPi.lean#L85-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/ArchimedeanBaseChange/ArchimedeanBaseChangeProof/HeckeFubiniCompatibility/PActPi.lean#L85-L97

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

theorem PositivityTheory.Rg.BcB.CG.update_psa_ne (w : ι) (j : Idx w) (J' : ∀ v : {v // v ≠ w}, Idx v) (v : {v // v ≠ w}) (x : Idx v) :
    Function.update ((Equiv.piSplitAt w Idx).symm (j, J')) (v : ι) x =
      (Equiv.piSplitAt w Idx).symm (j, Function.update J' v x) := by sorry
