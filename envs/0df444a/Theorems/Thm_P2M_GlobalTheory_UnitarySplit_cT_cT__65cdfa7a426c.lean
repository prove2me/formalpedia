-- Prove2me | Theorems.Thm_P2M_GlobalTheory_UnitarySplit_cT_cT__65cdfa7a426c
-- name    : P2M_GlobalTheory_UnitarySplit_cT_cT__65cdfa7a426c
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:11:41.196408+00:00
-- url     : https://prove2.me/theorems/d7ccb8f5-025f-4140-af69-9a10b5ec8382
-- title:
--   P2 M Global Theory Unitary Split c T c T  65cdfa7a426c: P2 M Global Theory Unitary Split c T c T  65cdfa7a426c
-- statement:
--   The P2 M Global Theory Unitary Split c T c T  65cdfa7a426c construction uses the P2 M Global Theory Unitary Split c T c T  65cdfa7a426c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/UnitarySupportedEquiv.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/UnitarySupportedEquiv.lean#L21-L23

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

theorem P2M_GlobalTheory_UnitarySplit_cT_cT__65cdfa7a426c (c : A →+* A) (hc : ∀ x, c (c x) = x) (M : Matrix (Fin n) (Fin n) A) :
    cT c (cT c M) = M := by sorry

alias «GlobalTheory».«UnitarySplit».«cT_cT'» := P2M_GlobalTheory_UnitarySplit_cT_cT__65cdfa7a426c
