-- Prove2me | Theorems.Thm_P2M_GlobalTheory_UnitarySplit_cT_smul__0f5a42997ef6
-- name    : P2M_GlobalTheory_UnitarySplit_cT_smul__0f5a42997ef6
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:11:33.3358+00:00
-- url     : https://prove2.me/theorems/8dccb42a-3c6b-4c01-afa4-e45562d4c850
-- title:
--   P2 M Global Theory Unitary Split c T smul  0f5a42997ef6: P2 M Global Theory Unitary Split c T smul  0f5a42997ef6
-- statement:
--   The P2 M Global Theory Unitary Split c T smul  0f5a42997ef6 construction uses the P2 M Global Theory Unitary Split c T smul  0f5a42997ef6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/UnitarySupportedEquiv.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/UnitarySupportedEquiv.lean#L17-L19

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_UnitarySupportedEquiv
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG
open GlobalTheory GlobalTheory.UnitarySplit
variable {A : Type} [CommRing A] {n : ℕ}

theorem P2M_GlobalTheory_UnitarySplit_cT_smul__0f5a42997ef6 (c : A →+* A) (a : A) (M : Matrix (Fin n) (Fin n) A) :
    cT c (a • M) = c a • cT c M := by sorry

alias «GlobalTheory».«UnitarySplit».«cT_smul'» := P2M_GlobalTheory_UnitarySplit_cT_smul__0f5a42997ef6
