-- Prove2me | Theorems.Thm_P2M_GlobalTheory_AdicQuot_eval__psi_3e690848319d
-- name    : P2M_GlobalTheory_AdicQuot_eval__psi_3e690848319d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:39:35.082803+00:00
-- url     : https://prove2.me/theorems/11268e78-f112-4175-84c4-140eedbdd07e
-- title:
--   P2 M Global Theory Adic Quot eval  psi 3e690848319d: P2 M Global Theory Adic Quot eval  psi 3e690848319d
-- statement:
--   The P2 M Global Theory Adic Quot eval  psi 3e690848319d construction uses the P2 M Global Theory Adic Quot eval  psi 3e690848319d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/AdicCompletionQuotientRingEquiv.lean#L42-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/AdicCompletionQuotientRingEquiv.lean#L42-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AdicCompletionQuotientRingEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.AdicQuot
open AdicCompletion
variable {A : Type} [CommRing A] (J q : Ideal A)

theorem P2M_GlobalTheory_AdicQuot_eval__psi_3e690848319d (n : ℕ) (x : AdicCompletion J A) :
    evalₐ _ n (psi J q x) = lev J q n x := by sorry

alias «GlobalTheory».«AdicQuot».«evalₐ_psi» := P2M_GlobalTheory_AdicQuot_eval__psi_3e690848319d
