-- Prove2me | Theorems.Thm_RandModSubsetSum_eq_61
-- name    : RandModSubsetSum.eq_61
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:03:05.110514+00:00
-- url     : https://prove2.me/theorems/9b341091-4515-4e40-a624-df0c0399463a
-- title:
--   Equation (61) — $F_\beta(n)\le 16e^{-n/(4\beta)}+26e^{-2\cdot10^{-20}(w_{\min}n-1)}+7\cdot2^{-10^{-15}n}\le2^{-c_Bn}$
-- statement:
--   Let $B>\delta_0$, $\beta=\max\{B,2\}$, $c_B=\min\{10^{-24},(100\beta)^{-1}\}$, and let $F_\beta(n)$ be the sum of the nine failure bounds of Table 10. For every $n\ge\max\{10^{26},10^6\beta\}$,
--
--   $$F_\beta(n)\le16e^{-n/(4\beta)}+26e^{-2\cdot10^{-20}(w_{\min}n-1)}+7\cdot2^{-10^{-15}n}\qquad(61)$$
--
--   and $F_\beta(n)\le2^{-c_Bn}$.
--
--   This is the explicit failure bound of Theorem 1.1: the failure of the whole algorithm is at most $F_\beta(n)$.
--
--   Differences from the source: none.
-- source:
--   Kim, Kim, Lee, Faster Provable Algorithm For Random Modular Subset Sum, STOC 2027 submission manuscript (sha256 c37a38c7…f89), Table 10, p. 68; (61), p. 69

import Mathlib
import Definitions.Def_RandModSubsetSum_Problem
import Definitions.Def_RandModSubsetSum_Overhead

namespace RandModSubsetSum

/-- **Equation (61) and the failure bound of Theorem 1.1**. Kim, Kim, Lee, *Faster Provable Algorithm For Random Modular Subset Sum*, STOC 2027 submission
manuscript (sha256 c37a38c7…f89), Appendix C.3, Table 10, p. 68, and
(61), p. 69.

Let `F_β(n)` be the sum of the nine bounds of Table 10. For `n ≥ max{10²⁶, 10⁶ β}`,
`F_β(n) ≤ 16 e^{−n/(4β)} + 26 e^{−2·10⁻²⁰(w_min n − 1)} + 7 · 2^{−10⁻¹⁵ n}` (61), and
`F_β(n) ≤ 2^{−c_B n}` with `c_B = min{10⁻²⁴, (100β)⁻¹}`.

**Formalization Note.** `β = max{B, 2}` with `B > δ₀`; `w_min = min_r w_r` for the weights of
Table 4. Decimals are exact rationals. -/
theorem eq_61 (B : ℝ) (hB : delta0 < B) (n : ℕ)
    (hn : max ((10 : ℝ) ^ 26) ((10 : ℝ) ^ 6 * beta B) ≤ n) :
    Fbeta (beta B) n ≤ 16 * Real.exp (-(n : ℝ) / (4 * beta B)) +
        26 * Real.exp (-(2 / 10 ^ 20) * (wmin * n - 1)) + 7 * (2 : ℝ) ^ (-(1 / 10 ^ 15) * (n : ℝ)) ∧
    Fbeta (beta B) n ≤ (2 : ℝ) ^ (-(cB B) * n) := by sorry

end RandModSubsetSum
