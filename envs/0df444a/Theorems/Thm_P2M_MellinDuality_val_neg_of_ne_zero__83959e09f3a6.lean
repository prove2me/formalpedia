-- Prove2me | Theorems.Thm_P2M_MellinDuality_val_neg_of_ne_zero__83959e09f3a6
-- name    : P2M_MellinDuality_val_neg_of_ne_zero__83959e09f3a6
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:43:59.835105+00:00
-- url     : https://prove2.me/theorems/212e6f23-e987-498f-8076-9b2c26602a5f
-- title:
--   P2 M Mellin Duality val neg of ne zero  83959e09f3a6: P2 M Mellin Duality val neg of ne zero  83959e09f3a6
-- statement:
--   The P2 M Mellin Duality val neg of ne zero  83959e09f3a6 construction uses the P2 M Mellin Duality val neg of ne zero  83959e09f3a6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Half.lean#L27-L28
-- source:
--   https://github.com/jkfarland-bot/MellinDuality/blob/1a5228293f894c9779404d39808b250705e30137/MellinDuality/Half.lean#L27-L28

module
public import Definitions.Def_MellinDuality_Defs
public import Definitions.Def_MellinDuality_Half
set_option autoImplicit true
@[expose] public section
public section
open MellinDuality
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem P2M_MellinDuality_val_neg_of_ne_zero__83959e09f3a6 {x : ZMod p} (hx : x ≠ 0) : (-x).val = p - x.val := by sorry

alias «MellinDuality».«val_neg_of_ne_zero'» := P2M_MellinDuality_val_neg_of_ne_zero__83959e09f3a6
