-- Prove2me | Theorems.Thm_P2M_Formalism_UG_P_permMatrix_mul_apply__c01338ce70d6
-- name    : P2M_Formalism_UG_P_permMatrix_mul_apply__c01338ce70d6
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:01:09.231511+00:00
-- url     : https://prove2.me/theorems/058b39ef-ba8d-4b87-831e-3ba251d44aa7
-- title:
--   P2 M Formalism UG P perm Matrix mul apply  c01338ce70d6: P2 M Formalism UG P perm Matrix mul apply  c01338ce70d6
-- statement:
--   The P2 M Formalism UG P perm Matrix mul apply  c01338ce70d6 construction uses the P2 M Formalism UG P perm Matrix mul apply  c01338ce70d6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/FIwasawaB.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/FIwasawaB.lean#L19-L21

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaA
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG Matrix
open Formalism Formalism.UG Formalism.UG.P
variable {L : Type} [Field L] (σ : L →+* L) {n : ℕ}

theorem P2M_Formalism_UG_P_permMatrix_mul_apply__c01338ce70d6 (π : Equiv.Perm (Fin n)) (M : Matrix (Fin n) (Fin n) L) (i j : Fin n) :
    (fIwasawaP π * M : Matrix (Fin n) (Fin n) L) i j = M (π i) j := by sorry

alias «Formalism».«UG».«P».«permMatrix_mul_apply₂» := P2M_Formalism_UG_P_permMatrix_mul_apply__c01338ce70d6
