-- Prove2me | Theorems.Thm_P2M_Sendov_c_six__13488b48dfc2
-- name    : P2M_Sendov_c_six__13488b48dfc2
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:15:46.393902+00:00
-- url     : https://prove2.me/theorems/382a6334-c51e-4f5f-aaed-ba85497a791e
-- title:
--   P2 M Sendov c six  13488b48dfc2: P2 M Sendov c six  13488b48dfc2
-- statement:
--   The P2 M Sendov c six  13488b48dfc2 construction uses the P2 M Sendov c six  13488b48dfc2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree6.lean#L41-L45
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree6.lean#L41-L45

import Definitions.Def_Sendov_Common_Basic
import Definitions.Def_Sendov_FiniteRange_Moments
import Definitions.Def_Sendov_FiniteRange_Degree6
set_option autoImplicit false
open Sendov
open MeasureTheory
variable {α : ℝ}

theorem P2M_Sendov_c_six__13488b48dfc2 (hα : 0 ≤ α) : c 6 α = (30 - α - 2 * α ^ 2) / (10 * (3 + α)) := by sorry

alias «Sendov».«c_six'» := P2M_Sendov_c_six__13488b48dfc2
