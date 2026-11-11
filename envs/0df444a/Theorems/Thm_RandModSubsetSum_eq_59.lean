-- Prove2me | Theorems.Thm_RandModSubsetSum_eq_59
-- name    : RandModSubsetSum.eq_59
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:03:16.408611+00:00
-- url     : https://prove2.me/theorems/01cccf52-807a-4332-bbdf-cf978c144fec
-- title:
--   Equation (59) — $\log_2\Pi_\beta(n)<100167+1500018\log_2n<10^{-4}n$
-- statement:
--   Let $B>\delta_0$ and $\beta=\max\{B,2\}$. For every $n\ge\max\{10^{26},10^6\beta\}$:
--
--   $$\beta\le n,\quad L_\beta(n)+1<2^{21}n^3,\quad\log_2A_\beta(n)<166+18\log_2n,$$
--   $$\log_2\Pi_\beta(n)<100167+1500018\log_2n<10^{-4}n,\qquad 14\log_2(n+1)+1<0.000005\,n.$$
--
--   The polynomial overhead $\Pi_\beta(n)$ of the implementation and the factor $(n+1)^{14}$ of the reductions are therefore absorbed by the gaps $0.2614-0.261398$ and $0.2373-0.23729$ in the exponents of Theorem 1.1.
--
--   Differences from the source:
--   - generalization: (59) → (59) together with the companion inequality 14 log₂(n + 1) + 1 < 0.000005 n of p. 69; reason: both are used together for the resource bound; the statement implies (59)
-- source:
--   Kim, Kim, Lee, Faster Provable Algorithm For Random Modular Subset Sum, STOC 2027 submission manuscript (sha256 c37a38c7…f89), Appendix C.2, (56), (58), (59), pp. 65–67; p. 69

import Mathlib
import Definitions.Def_RandModSubsetSum_Problem
import Definitions.Def_RandModSubsetSum_Overhead

namespace RandModSubsetSum

/-- **Equation (59)** (the polynomial overhead is below `2^{10⁻⁴ n}`). Kim, Kim, Lee, *Faster Provable Algorithm For Random Modular Subset Sum*, STOC 2027 submission
manuscript (sha256 c37a38c7…f89), Appendix C.2, (56),
(58), (59), pp. 65–67; and the companion inequality on p. 69.

For `n ≥ max{10²⁶, 10⁶ β}`: `β ≤ n`, `L_β(n) + 1 < 2^{21} n³`, `log₂ A_β(n) < 166 + 18 log₂ n`,
`log₂ Π_β(n) < 100167 + 1500018 log₂ n < 10⁻⁴ n`, and `14 log₂(n + 1) + 1 < 0.000005 n`.

**Formalization Note.** `β = max{B, 2}` with `B > δ₀` real; `L_β(n)` is a ceiling of a real. -/
theorem eq_59 (B : ℝ) (hB : delta0 < B) (n : ℕ)
    (hn : max ((10 : ℝ) ^ 26) ((10 : ℝ) ^ 6 * beta B) ≤ n) :
    beta B ≤ n ∧
    (Lbeta (beta B) n : ℝ) + 1 < (2 : ℝ) ^ 21 * (n : ℝ) ^ 3 ∧
    Real.logb 2 (Abeta (beta B) n) < 166 + 18 * Real.logb 2 n ∧
    Real.logb 2 (Pibeta (beta B) n) < 100167 + 1500018 * Real.logb 2 n ∧
    100167 + 1500018 * Real.logb 2 n < (1 / 10 ^ 4) * n ∧
    14 * Real.logb 2 ((n : ℝ) + 1) + 1 < (5 / 10 ^ 6) * n := by sorry

end RandModSubsetSum
