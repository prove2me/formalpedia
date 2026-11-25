-- Prove2me | Theorems.Thm_P2M_GlobalTheory_AlgConn_hom_eq_toSpec__comp_f14dc953d336
-- name    : P2M_GlobalTheory_AlgConn_hom_eq_toSpec__comp_f14dc953d336
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:02:17.699605+00:00
-- url     : https://prove2.me/theorems/6b57aacd-2054-4303-81f7-758cc9d1f057
-- title:
--   P2 M Global Theory Alg Conn hom eq to Spec  comp f14dc953d336: P2 M Global Theory Alg Conn hom eq to Spec  comp f14dc953d336
-- statement:
--   The P2 M Global Theory Alg Conn hom eq to Spec  comp f14dc953d336 construction uses the P2 M Global Theory Alg Conn hom eq to Spec  comp f14dc953d336 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HomExtSpecProdSelfOfBasicOpenPreimageEq.lean#L13-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HomExtSpecProdSelfOfBasicOpenPreimageEq.lean#L13-L15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsClopenBasicOpenSpecProdSelfFirstIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIdempotentOfClopen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdempotentEqOfBasicOpenEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HomExtSpecProdSelfOfBasicOpenPreimageEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.AlgConn
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.AlgConn

theorem P2M_GlobalTheory_AlgConn_hom_eq_toSpec__comp_f14dc953d336 {T : Scheme.{0}} {A : CommRingCat.{0}} (h : T ⟶ Spec A) :
    h = T.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso A).inv ≫ h.appTop) := by sorry

alias «GlobalTheory».«AlgConn».«hom_eq_toSpecΓ_comp» := P2M_GlobalTheory_AlgConn_hom_eq_toSpec__comp_f14dc953d336
