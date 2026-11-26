-- Prove2me | Theorems.Thm_TDLC_Syntax_erase_elaborate
-- name    : TDLC.Syntax.erase_elaborate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:26:54.314801+00:00
-- url     : https://prove2.me/theorems/95abee8c-856f-5489-ac27-c3a16121d00e
-- title:
--   Syntax: erase elaborate
-- statement:
--   The Syntax construction uses the erase elaborate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Syntax.lean#L71-L75
-- source:
--   https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Syntax.lean#L71-L75

import Definitions.Def_TDLC_Solution
import Definitions.Def_TDLC_Syntax
set_option autoImplicit true
open TDLC TDLC.Syntax

theorem TDLC.Syntax.erase_elaborate (h : HasType Γ r a) : erase (elaborate h) = r := by sorry
