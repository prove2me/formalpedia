-- Prove2me | Theorems.Thm_P2M_Formalism_UG_P_permMatrix_mulVec__7012a139132f
-- name    : P2M_Formalism_UG_P_permMatrix_mulVec__7012a139132f
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:01:33.339028+00:00
-- url     : https://prove2.me/theorems/49298260-c07a-464a-9a7d-5b6ac4e7f2f0
-- title:
--   P2 M Formalism UG P perm Matrix mul Vec  7012a139132f: P2 M Formalism UG P perm Matrix mul Vec  7012a139132f
-- statement:
--   The P2 M Formalism UG P perm Matrix mul Vec  7012a139132f construction uses the P2 M Formalism UG P perm Matrix mul Vec  7012a139132f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/FIwasawaB.lean#L14-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/FIwasawaB.lean#L14-L17

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

theorem P2M_Formalism_UG_P_permMatrix_mulVec__7012a139132f (π : Equiv.Perm (Fin n)) (w : Fin n → L) :
    fIwasawaP π *ᵥ w = fun i => w (π i) := by sorry

alias «Formalism».«UG».«P».«permMatrix_mulVec₂» := P2M_Formalism_UG_P_permMatrix_mulVec__7012a139132f
