-- Prove2me | Theorems.Thm_P2M_GlobalTheory_AlgConn_hom_ext_of_two__of_basicOpen_d5662058710f
-- name    : P2M_GlobalTheory_AlgConn_hom_ext_of_two__of_basicOpen_d5662058710f
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:02:02.692485+00:00
-- url     : https://prove2.me/theorems/fb339203-dc56-4cd9-a8a4-0ebee52cff69
-- title:
--   P2 M Global Theory Alg Conn hom ext of two  of basic Open d5662058710f: P2 M Global Theory Alg Conn hom ext of two  of basic Open d5662058710f
-- statement:
--   The P2 M Global Theory Alg Conn hom ext of two  of basic Open d5662058710f construction uses the P2 M Global Theory Alg Conn hom ext of two  of basic Open d5662058710f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HomExtSpecProdSelfOfBasicOpenPreimageEq.lean#L17-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HomExtSpecProdSelfOfBasicOpenPreimageEq.lean#L17-L56

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

theorem P2M_GlobalTheory_AlgConn_hom_ext_of_two__of_basicOpen_d5662058710f : ∀ (O : Type) [CommRing O] (T : Scheme.{0})
    (h h' : T ⟶ Spec (.of (O × O))), h ≫ twoπ O = h' ≫ twoπ O →
    h ⁻¹ᵁ (Spec (.of (O × O))).basicOpen (fst1 O) = h' ⁻¹ᵁ (Spec (.of (O × O))).basicOpen (fst1 O) →
    h = h' := by sorry

alias «GlobalTheory».«AlgConn».«hom_ext_of_twoπ_of_basicOpen» := P2M_GlobalTheory_AlgConn_hom_ext_of_two__of_basicOpen_d5662058710f
