-- Prove2me | Theorems.Thm_ThreeSumSharpTail_pruned_lop_detection
-- name    : ThreeSumSharpTail.pruned_lop_detection
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-13T21:25:54.170131+00:00
-- url     : https://prove2.me/theorems/5bec0f68-6b2f-4745-923a-e3684afb4554
-- title:
--   A native global Lop detector from finite sharp-tail cost parameters
-- statement:
--   Given a finite RatParams record and rational 0<a<1, 0<s<1/2 with CostsWithinP on every 1<=D<=N^a, the actual light model has a global Lop detector. On that regime its time is bounded by a uniform nonnegative constant times preprocessing, all query costs, and ND+w+1 overhead. Outside the regime an actual finite program branch supplies correctness through the brute routine.
-- source:
--   Native ThinInst/TaskN program assembly using an exact integer-power regime test, the arbitrary-parameter pruned resource theorem and actual count-to-detection execution semantics.

import Definitions.Def_APSP299791_Defs5

theorem ThreeSumSharpTail.pruned_lop_detection
    (G : Light.Sec4.RatParams) (a s : ℚ)
    (ha0 : 0 < a) (ha1 : a < 1) (hs0 : 0 < s) (hsHalf : s < 1 / 2)
    (hcost : ∃ C : ℝ, 0 ≤ C ∧ ∀ N D : ℕ,
      1 ≤ D → (D : ℝ) ≤ (N : ℝ) ^ (a : ℝ) →
      Light.Sec4.CostsWithinP G C N D
        ((N : ℝ) ^ 2 * (Real.log D + 1) ^ 2 / (D : ℝ) ^ (s : ℝ))
        ((D : ℝ) ^ (1 / 2 - (s : ℝ)) * (Real.log D + 1))) :
    ∃ (C : ℝ) (Td : ℕ → ℕ → ℕ → ℝ), 0 ≤ C ∧ Light.lightModel.lopDetect Td ∧
      ∀ n d w : ℕ, 1 ≤ d → (d : ℝ) ≤ (n : ℝ) ^ (a : ℝ) →
        Td n d w ≤ C * ((n : ℝ) ^ 2 * (Real.log d + 1) ^ 2 / (d : ℝ) ^ (s : ℝ) +
          (w : ℝ) * (d : ℝ) ^ (1 / 2 - (s : ℝ)) * (Real.log d + 1) + (n : ℝ) * d + w + 1) := by sorry
