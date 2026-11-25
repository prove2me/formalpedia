-- Prove2me | Theorems.Thm_P2M_GlobalTheory_UnitarySplit_cT_add__9947e56985ad
-- name    : P2M_GlobalTheory_UnitarySplit_cT_add__9947e56985ad
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:11:35.403029+00:00
-- url     : https://prove2.me/theorems/3d1eab5d-de3d-4848-b0e2-cbeb5f17faf8
-- title:
--   P2 M Global Theory Unitary Split c T add  9947e56985ad: P2 M Global Theory Unitary Split c T add  9947e56985ad
-- statement:
--   The P2 M Global Theory Unitary Split c T add  9947e56985ad construction uses the P2 M Global Theory Unitary Split c T add  9947e56985ad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/UnitarySupportedEquiv.lean#L13-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/UnitarySupportedEquiv.lean#L13-L15

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

theorem P2M_GlobalTheory_UnitarySplit_cT_add__9947e56985ad (c : A →+* A) (M N : Matrix (Fin n) (Fin n) A) :
    cT c (M + N) = cT c M + cT c N := by sorry

alias «GlobalTheory».«UnitarySplit».«cT_add'» := P2M_GlobalTheory_UnitarySplit_cT_add__9947e56985ad
