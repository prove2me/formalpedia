-- Prove2me | Theorems.Thm_TDLC_Syntax_representationAdequacy
-- name    : TDLC.Syntax.representationAdequacy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:27:03.32202+00:00
-- url     : https://prove2.me/theorems/07879f6e-45c8-5c96-b85b-7b52d917fcb3
-- title:
--   Syntax: representation Adequacy
-- statement:
--   Representation adequacy: exactly the extrinsically well-typed trees are represented.
--
--   Source: https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Syntax.lean#L78-L84
-- source:
--   https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Syntax.lean#L78-L84

import Definitions.Def_TDLC_Solution
import Definitions.Def_TDLC_Syntax
set_option autoImplicit true
open TDLC TDLC.Syntax

theorem TDLC.Syntax.representationAdequacy (Γ : List Ty) (r : Raw) (a : Ty) :
    Nonempty (HasType Γ r a) ↔ ∃ t : Tm Γ a, erase t = r := by sorry
