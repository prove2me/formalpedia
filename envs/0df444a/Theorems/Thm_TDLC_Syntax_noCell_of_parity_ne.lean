-- Prove2me | Theorems.Thm_TDLC_Syntax_noCell_of_parity_ne
-- name    : TDLC.Syntax.noCell_of_parity_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:26:58.035479+00:00
-- url     : https://prove2.me/theorems/c12a5094-1afe-5ed2-8b29-b5b2bcf9634a
-- title:
--   Syntax: no Cell of parity ne
-- statement:
--   Different grades reflect non-identification by the full host two-cell theory.
--
--   Source: https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Syntax.lean#L248-L256
-- source:
--   https://github.com/Arthur742Ramos/two-dimensional-lambda-calculus-lean/blob/7aa1f961347b19deab3718521627b98f14357bc7/Syntax.lean#L248-L256

import Definitions.Def_TDLC_Solution
import Definitions.Def_TDLC_Syntax
set_option autoImplicit true
open TDLC TDLC.Syntax

theorem TDLC.Syntax.noCell_of_parity_ne {t s : Tm Γ a} (c d : Conv t s)
    (hne : c.parity ≠ d.parity) (ρ : Env U Γ) :
    ¬ Nonempty (TDLC.Path2 (TDLC.Path.lEmbed (interpret c ρ))
      (TDLC.Path.lEmbed (interpret d ρ))) := by sorry
