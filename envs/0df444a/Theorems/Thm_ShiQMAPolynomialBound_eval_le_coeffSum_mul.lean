-- Prove2me | Theorems.Thm_ShiQMAPolynomialBound_eval_le_coeffSum_mul
-- name    : ShiQMAPolynomialBound.eval_le_coeffSum_mul
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-01T01:28:46.217608+00:00
-- url     : https://prove2.me/theorems/b468078d-4547-435d-aeaf-9a40360bf4ff
-- title:
--   Bound a natural polynomial by its coefficient sum and degree
-- statement:
--   For any polynomial $p$ with natural-number coefficients and natural input $n$, its value at $n$ is at most $p(1)(n+1)^d$, where $d$ is the natural degree of $p$. The bound supplies a fixed coefficient and degree budget for a computable QMA amplification schedule.
-- source:
--   Yueheng Shi, QMA amplification Lean source, https://github.com/shiy1022/qma-amplification-lean/blob/83191f2e3fdc36033c8a99e8f9af6625d2cda2b0/proofs/AMPUNI-polynomial-eval-upper.lean#L9-L39; used in the copy-based QMA amplification round schedule

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Data.Nat.Log

set_option autoImplicit false

/-- A fixed natural-coefficient polynomial is bounded by its coefficient sum
times one power of `n+1`. -/

theorem ShiQMAPolynomialBound.eval_le_coeffSum_mul (p : Polynomial ℕ) (n : ℕ) :
    p.eval n ≤ p.eval 1 * (n + 1) ^ p.natDegree := by
  sorry
