-- Prove2me | Theorems.Thm_P2M_Sendov_c_twenty__12ee6a925b10
-- name    : P2M_Sendov_c_twenty__12ee6a925b10
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:00:54.779103+00:00
-- url     : https://prove2.me/theorems/a73fd725-7f3d-5c08-acc8-de6e3b5efb80
-- title:
--   P2 M Sendov c twenty  12ee6a925b10: P2 M Sendov c twenty  12ee6a925b10
-- statement:
--   The P2 M Sendov c twenty  12ee6a925b10 construction uses the P2 M Sendov c twenty  12ee6a925b10 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree20.lean#L46-L50
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree20.lean#L46-L50

import Definitions.Def_Sendov_FiniteRange_Reduce
import Definitions.Def_Sendov_FiniteRange_Degree20
set_option autoImplicit false
set_option maxRecDepth 8000
open Sendov
open MeasureTheory
variable {α : ℝ}

theorem P2M_Sendov_c_twenty__12ee6a925b10 (hα : 0 ≤ α) : c 20 α = (114 + 13 * α - 2 * α ^ 2) / (38 * (3 + α)) := by sorry

alias «Sendov».«c_twenty'» := P2M_Sendov_c_twenty__12ee6a925b10
