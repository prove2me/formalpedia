-- Prove2me | Theorems.Thm_TaoFivePrimes_step_T_certificate
-- name    : TaoFivePrimes.step_T_certificate
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-29T12:54:04.340483+00:00
-- url     : https://prove2.me/theorems/c25ae31e-be2c-42ac-84a4-4d9cc3e4f678
-- title:
--   Exact recurrence for the partial reciprocal-prime sums below 512
-- statement:
--   For every $k<511$, the rational table $T$ of partial reciprocal-prime sums satisfies the exact one-step recurrence
--   $$T(k+1)\ =\ T(k)\ +\ \begin{cases}\dfrac{1}{k+1}, & k+1\ \text{prime},\\[2mm] 0, & \text{otherwise},\end{cases}$$
--   with all values understood in $\mathbb{Q}$ and $T(n)=\sum_{p\le n}1/p$ for $0\le n\le 511$.
--
--   This recurrence is what identifies the tabulated values $T(n)$ with the partial sums of the reciprocal primes in the finite endpoint certificate; it is a 511-case arithmetic verification.
--
--   **Formalization Note.** The table `T : \mathbb{N} \to \mathbb{Q}` is stored in `TaoFivePrimes_mertens_cert_511_tables`; the case distinction uses `Nat.Prime` and the hypothesis $hk : k < 511$ keeps the recursion inside the tabulated range.

import Mathlib
import Definitions.Def_TaoFivePrimes_mertens_cert_511_tables

namespace TaoFivePrimes

theorem step_T_certificate (k : Nat) (hk : k < 511) :
    T (k+1) = T k + if (k+1).Prime then (1:Rat)/((k+1 : Nat) : Rat) else 0 := by
  sorry

end TaoFivePrimes
