-- Prove2me | Theorems.Thm_Sendov_Jsum_estimate
-- name    : Sendov.Jsum_estimate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:57:31.467574+00:00
-- url     : https://prove2.me/theorems/2bbc7dfa-4442-4d9b-bafe-edd791400c38
-- title:
--   Sendov: Jsum estimate
-- statement:
--   **The estimate for `J ∑ⱼ 1/zⱼ`.**  Conjugating the centroid identity replaces `1/zⱼ` by
--   `conj zⱼ` and `qⱼ` by `1/conj qⱼ`; the defect lemma pays for both substitutions at once.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Jsum.lean#L122-L250
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Jsum.lean#L122-L250

import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Defect
import Definitions.Def_Sendov_Analytic_Polar
import Definitions.Def_Sendov_Analytic_Jsum
set_option autoImplicit false
open Sendov

theorem Sendov.Jsum_estimate {n : ℕ} (hn : 2 ≤ n) {a x y : ℝ} {z q : Multiset ℂ}
    (hqcard : q.card = n - 1)
    (hz1 : ∀ w ∈ z, ‖w‖ ≤ 1) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1)
    (hcent : ((n : ℂ) - 1) * ((a : ℂ) + z.sum) = (n : ℂ) * (q.map (fun v => (a : ℂ) - v⁻¹)).sum)
    (hxy : q.sum = ((n : ℂ) - 1) * ((x : ℂ) + (y : ℂ) * Complex.I)) :
    ‖q.prod * sumEraseProd z
        - ((a : ℂ) * ((n : ℂ) - 1) - (n : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I))
            * (q.prod * z.prod)‖
      ≤ ((n : ℝ) / ((n : ℝ) - 1)) * (1 - (‖q.prod‖ * ‖z.prod‖) ^ 2) := by sorry
