-- Prove2me | Theorems.Thm_TDLC_Syntax_interpret_parity
-- name    : TDLC.Syntax.interpret_parity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:26:55.775325+00:00
-- url     : https://prove2.me/theorems/e2cab9a4-3b6c-50dd-961b-a76dad3f2776
-- title:
--   Syntax: interpret parity
-- statement:
--   The Syntax construction uses the interpret parity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Syntax.lean#L231-L245
-- source:
--   https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Syntax.lean#L231-L245

import Definitions.Def_TDLC_Solution
import Definitions.Def_TDLC_Syntax
set_option autoImplicit true
open TDLC TDLC.Syntax

theorem TDLC.Syntax.interpret_parity {t s : Tm Γ a} (c : Conv t s) (ρ : Env U Γ) :
    TDLC.Step.parity (interpret c ρ) = c.parity := by sorry
