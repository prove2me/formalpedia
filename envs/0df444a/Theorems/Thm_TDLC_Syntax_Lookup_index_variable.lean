-- Prove2me | Theorems.Thm_TDLC_Syntax_Lookup_index_variable
-- name    : TDLC.Syntax.Lookup.index_variable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:26:51.987444+00:00
-- url     : https://prove2.me/theorems/ccc39dc8-3697-5993-840b-f656821c7282
-- title:
--   Lookup: index variable
-- statement:
--   The Lookup construction uses the index variable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Syntax.lean#L56-L59
-- source:
--   https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Syntax.lean#L56-L59

import Definitions.Def_TDLC_Solution
import Definitions.Def_TDLC_Syntax
set_option autoImplicit true
open TDLC TDLC.Syntax

theorem TDLC.Syntax.Lookup.index_variable (h : Lookup Γ n a) : h.variable.index = n := by sorry
