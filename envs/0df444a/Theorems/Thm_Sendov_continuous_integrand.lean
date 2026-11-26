-- Prove2me | Theorems.Thm_Sendov_continuous_integrand
-- name    : Sendov.continuous_integrand
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:54:54.290976+00:00
-- url     : https://prove2.me/theorems/0e874c34-69a7-4964-b381-0232cea78439
-- title:
--   Sendov: continuous integrand
-- statement:
--   The integrand of `Sendov.R` is continuous, hence interval integrable.  Needed wherever an
--   integral involving `Q ^ e` is split or compared.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Common/Rpow.lean#L49-L54
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Common/Rpow.lean#L49-L54

import Definitions.Def_Sendov_Common_Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_Sendov_Common_Rpow
set_option autoImplicit false
open Sendov
open MeasureTheory

theorem Sendov.continuous_integrand (n : ℕ) (α : ℝ) {e : ℝ} (he : 0 ≤ e) :
    Continuous fun t : ℝ => t ^ 3 * Q n α t ^ e := by sorry
