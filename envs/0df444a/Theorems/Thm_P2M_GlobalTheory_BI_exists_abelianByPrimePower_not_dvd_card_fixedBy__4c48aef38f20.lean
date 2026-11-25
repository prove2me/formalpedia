-- Prove2me | Theorems.Thm_P2M_GlobalTheory_BI_exists_abelianByPrimePower_not_dvd_card_fixedBy__4c48aef38f20
-- name    : P2M_GlobalTheory_BI_exists_abelianByPrimePower_not_dvd_card_fixedBy__4c48aef38f20
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:02:28.052873+00:00
-- url     : https://prove2.me/theorems/c0dfe13a-b936-41bb-9c44-2d21b7a5592b
-- title:
--   P2 M Global Theory BI exists abelian By Prime Power not dvd card fixed By  4c48aef38f20: P2 M Global Theory BI exists abelian By Prime Power not dvd card fixed By  4c48aef38f20
-- statement:
--   The P2 M Global Theory BI exists abelian By Prime Power not dvd card fixed By  4c48aef38f20 construction uses the P2 M Global Theory BI exists abelian By Prime Power not dvd card fixed By  4c48aef38f20 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsAbelianByPrimePowerNotDvdCardFixedBy.lean#L10-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsAbelianByPrimePowerNotDvdCardFixedBy.lean#L10-L45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CardFixedByQuotientEqRelIndexOfPRegularStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CardFixedByPowPrimePowModEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsCoprimeOrderOfPowPrimePowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsSylowOverSubgroupStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsAbelianByPrimePowerNotDvdCardFixedBy
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.BI
open GlobalTheory GlobalTheory.BI

theorem P2M_GlobalTheory_BI_exists_abelianByPrimePower_not_dvd_card_fixedBy__4c48aef38f20 :
    ∀ (G : Type) [Group G] [Finite G] (x : G) (p : ℕ), p.Prime →
      ∃ H : Subgroup G, AbByP H ∧ ¬ p ∣ Nat.card (MulAction.fixedBy (G ⧸ H) x) := by sorry

alias «GlobalTheory».«BI».«exists_abelianByPrimePower_not_dvd_card_fixedBy₂» := P2M_GlobalTheory_BI_exists_abelianByPrimePower_not_dvd_card_fixedBy__4c48aef38f20
