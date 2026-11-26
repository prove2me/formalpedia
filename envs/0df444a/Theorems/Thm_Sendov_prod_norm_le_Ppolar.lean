-- Prove2me | Theorems.Thm_Sendov_prod_norm_le_Ppolar
-- name    : Sendov.prod_norm_le_Ppolar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:54:00.151668+00:00
-- url     : https://prove2.me/theorems/3d6250b6-a890-4b35-9c06-0e6a092b61a9
-- title:
--   Sendov: prod norm le Ppolar
-- statement:
--   **The pointwise quadratic-mean bound.**  `∏ⱼ |a + t(1-a²)qⱼ| ≤ P(t)^{(n-1)/2)}`, by AM–GM
--   on the squares followed by `∑ ‖qⱼ‖² ≤ n-1`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Polar.lean#L209-L271
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Polar.lean#L209-L271

import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Maclaurin
import Definitions.Def_Sendov_Reduction_Setup
import Definitions.Def_Sendov_Analytic_Polar
set_option autoImplicit false
open Sendov
open Polynomial MeasureTheory

theorem Sendov.prod_norm_le_Ppolar {n : ℕ} (hn : 2 ≤ n) {a x t : ℝ}
    {q : Multiset ℂ} (hqcard : q.card = n - 1) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1)
    (hx : (q.map (fun v => v.re)).sum = ((n : ℝ) - 1) * x) :
    (q.map (fun v => ‖(a : ℂ) + (t : ℂ) * (1 - (a : ℂ) ^ 2) * v‖)).prod
      ≤ Ppolar a x t ^ (((n : ℝ) - 1) / 2) := by sorry
