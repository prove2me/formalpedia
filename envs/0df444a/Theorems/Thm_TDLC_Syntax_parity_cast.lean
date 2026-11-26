-- Prove2me | Theorems.Thm_TDLC_Syntax_parity_cast
-- name    : TDLC.Syntax.parity_cast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:26:55.406341+00:00
-- url     : https://prove2.me/theorems/47c38008-8976-41e2-9fbf-9a5fa6718ee1
-- title:
--   Syntax: parity cast
-- statement:
--   The Syntax construction uses the parity cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Syntax.lean#L224-L229
-- source:
--   https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Syntax.lean#L224-L229

import Definitions.Def_TDLC_Solution
import Definitions.Def_TDLC_Syntax
set_option autoImplicit true
open TDLC TDLC.Syntax

theorem TDLC.Syntax.parity_cast {A : Type} {x y x' y' : A}
    (hx : x = x') (hy : y = y') (s : TDLC.Step x y) :
    TDLC.Step.parity (castStep hx hy s) = TDLC.Step.parity s := by sorry
