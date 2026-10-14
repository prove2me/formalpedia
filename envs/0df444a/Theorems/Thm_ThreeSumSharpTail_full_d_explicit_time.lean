-- Prove2me | Theorems.Thm_ThreeSumSharpTail_full_d_explicit_time
-- name    : ThreeSumSharpTail.full_d_explicit_time
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-13T19:25:22.672927+00:00
-- url     : https://prove2.me/theorems/b7b75205-3d84-4d1e-8313-846ecda2467d
-- title:
--   Generic full dimension costs give the explicit Exact Triangle exponent
-- statement:
--   Let 0<a<=1, 0<=s<=1/2, D(n)=floor(n^a), g(n)=ceil(D(n)^(s/2)), and suppose the actual model has the full-D Theorem 17 host and Lop detection with preprocessing n^2(log D+1)^2/D^s, query D^(1/2-s)(log D+1), and nD+w+1 overhead on D<=n^a. If a(1+s)<=1 and log_2(7)+3a/2<=3-as/2, then one actual Exact Triangle solver has time O(kappa n^(3-as/2) log^2 n) from some fixed size onward, uniformly in kappa>=1 and input weight magnitude u<=n^kappa.
-- source:
--   Generic full-D Theorem 19 deduction for Xu, same manuscript, Sections 3-4. Includes floor/ceiling effects and all host terms; reuses the proved full-D call and extra-cost bounds.

import Definitions.Def_APSP299791_Defs4
import Theorems.Thm_ThreeSumSharpTail_full_d_call_total
import Theorems.Thm_ThreeSumSharpTail_full_d_extra_total
import Mathlib
open ThreeSumApsp Filter

theorem ThreeSumSharpTail.full_d_explicit_time (M : DetTimeModel) (a s : ℝ) (D g : ℕ → ℕ)
    (ha0 : 0 < a) (ha1 : a ≤ 1) (hs0 : 0 ≤ s) (hsHalf : s ≤ 1 / 2)
    (hDfloor : ∀ n, D n = ⌊(n : ℝ) ^ a⌋₊)
    (hgceil : ∀ n, 1 ≤ D n → g n = ⌈(D n : ℝ) ^ (s / 2)⌉₊)
    (hprime : Real.logb 2 7 + 3 * a / 2 ≤ 3 - a * s / 2)
    (hbuild : a * (1 + s) ≤ 1)
    (h17 : Claim.Theorem_17 M strassen D g)
    (hlop : ∃ (C : ℝ) (Td : ℕ → ℕ → ℕ → ℝ), 0 ≤ C ∧ M.lopDetect Td ∧
      ∀ n d w : ℕ, 1 ≤ d → (d : ℝ) ≤ (n : ℝ) ^ a →
        Td n d w ≤ C * ((n : ℝ) ^ 2 * (Real.log d + 1) ^ 2 / (d : ℝ) ^ s +
          (w : ℝ) * (d : ℝ) ^ (1 / 2 - s) * (Real.log d + 1) + (n : ℝ) * d + w + 1)) :
    ∃ n₀, Claim.Theorem_19_explicitAt M (a * s / 2) 2 n₀ := by sorry
