-- Prove2me | Theorems.Thm_P2M_ConfFamily_inter_diff_union__310b7debc330
-- name    : P2M_ConfFamily_inter_diff_union__310b7debc330
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T20:42:08.163818+00:00
-- url     : https://prove2.me/theorems/88d98ac3-391f-4ef9-bf79-a5164bab83aa
-- title:
--   P2 M Conf Family inter diff union  310b7debc330: P2 M Conf Family inter diff union  310b7debc330
-- statement:
--   Re-adding the other one.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Stable/LTSI.lean#L89-L92
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Stable/LTSI.lean#L89-L92

import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_Family_LTSI
import Definitions.Def_EventStructures_Stable_LTSI
set_option autoImplicit true
open ConfFamily
variable {L : Type*} (F : ConfFamily L)
open ConfFamily
variable {F}

theorem P2M_ConfFamily_inter_diff_union__310b7debc330 {c : Set F.Event} {e₁ e₂ : F.Event}
    (he₁ : e₁ ∈ c) (hne : e₁ ≠ e₂) :
    ((c \ {e₁}) ∩ (c \ {e₂})) ∪ {e₁} = c \ {e₂} := by sorry

alias «ConfFamily».«inter_diff_union'» := P2M_ConfFamily_inter_diff_union__310b7debc330
