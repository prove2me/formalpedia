-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CayleyUnitary_cT_sub__9304f5a5c678
-- name    : P2M_GlobalTheory_CayleyUnitary_cT_sub__9304f5a5c678
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:37:19.811541+00:00
-- url     : https://prove2.me/theorems/0d112993-2fe3-4eca-aea3-2e33593b45ac
-- title:
--   P2 M Global Theory Cayley Unitary c T sub  9304f5a5c678: P2 M Global Theory Cayley Unitary c T sub  9304f5a5c678
-- statement:
--   The P2 M Global Theory Cayley Unitary c T sub  9304f5a5c678 construction uses the P2 M Global Theory Cayley Unitary c T sub  9304f5a5c678 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CayleyTransformSkewMemUnitaryGroup.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CayleyTransformSkewMemUnitaryGroup.lean#L15-L17

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CayleyTransformSkewMemUnitaryGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open NumberField
open GlobalTheory GlobalTheory.CayleyUnitary
open Formalism.UG

theorem P2M_GlobalTheory_CayleyUnitary_cT_sub__9304f5a5c678 {E : Type} [Field E] (σ : E →+* E) {n : ℕ} (A B : Matrix (Fin n) (Fin n) E) :
    cT σ (A - B) = cT σ A - cT σ B := by sorry

alias «GlobalTheory».«CayleyUnitary».«cT_sub'» := P2M_GlobalTheory_CayleyUnitary_cT_sub__9304f5a5c678
