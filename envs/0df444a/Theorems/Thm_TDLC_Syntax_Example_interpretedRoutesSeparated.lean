-- Prove2me | Theorems.Thm_TDLC_Syntax_Example_interpretedRoutesSeparated
-- name    : TDLC.Syntax.Example.interpretedRoutesSeparated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:27:10.124692+00:00
-- url     : https://prove2.me/theorems/4ec6413a-96f3-44f2-bf8c-b64233cf0ab8
-- title:
--   Example: interpreted Routes Separated
-- statement:
--   The Example construction uses the interpreted Routes Separated property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Syntax.lean#L280-L283
-- source:
--   https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Syntax.lean#L280-L283

import Definitions.Def_TDLC_Solution
import Definitions.Def_TDLC_Syntax
set_option autoImplicit true
open TDLC TDLC.Syntax
open TDLC.Syntax.Example

theorem TDLC.Syntax.Example.interpretedRoutesSeparated (ρ : Env U Γ) :
    ¬ Nonempty (TDLC.Path2 (TDLC.Path.lEmbed (interpret betaRoute ρ))
      (TDLC.Path.lEmbed (interpret etaRoute ρ))) := by sorry
