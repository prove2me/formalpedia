-- Prove2me | Theorems.Thm_Sendov_hasDerivAt_Fprod
-- name    : Sendov.hasDerivAt_Fprod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:56:54.7738+00:00
-- url     : https://prove2.me/theorems/73ba5c70-af29-4e79-af63-c4576423c33b
-- title:
--   Sendov: has Deriv At Fprod
-- statement:
--   `F'(t) = -a ∑ⱼ qⱼ ∏_{k≠j}(1 - a t q_k)`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Origin.lean#L299-L326
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Origin.lean#L299-L326

import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Maclaurin
import Definitions.Def_Sendov_Analytic_Defect
import Definitions.Def_Sendov_Common_Quadratic
import Definitions.Def_Sendov_Analytic_Polar
import Definitions.Def_Sendov_Analytic_Origin
set_option autoImplicit false
open Sendov

theorem Sendov.hasDerivAt_Fprod (a t : ℝ) : ∀ (q : Multiset ℂ),
    HasDerivAt (Fprod a q)
      (-(a : ℂ) * sumEraseProdC q id (fun v => 1 - (a : ℂ) * (t : ℂ) * v)) t := by sorry
