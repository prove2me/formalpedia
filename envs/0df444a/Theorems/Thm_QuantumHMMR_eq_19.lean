-- Prove2me | Theorems.Thm_QuantumHMMR_eq_19
-- name    : QuantumHMMR.eq_19
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T06:35:21.6272+00:00
-- url     : https://prove2.me/theorems/b86876bb-f795-4bd1-950a-53ddae01244a
-- title:
--   Eq. (19) — few insertions: $\Pr[J > 2T/m] \le (e/4)^{T/m}$
-- statement:
--   Let $J$ be the number of insertions among the $T$ updates of the walk. Since the updates are independent and each is an insertion with probability $1/m$, $J \sim \mathrm{Bin}(T, 1/m)$, so $\mathbb E[J] = T/m$, and the Chernoff bound gives
--   $$
--   \Pr[J > 2T/m] \le (e/4)^{T/m}. \tag{19}
--   $$
--   At $T = 3m\lceil\log^2 n\rceil$ this is $e^{-\Omega(\log^2 n)}$: there is $c > 0$ with $(e/4)^{T/m} \le e^{-c\log^2 n}$.
--
--   Outside this event the walk contains at most $2T/m$ non-Clifford gates, which is what the distinguisher exploits.
--
--   Differences from the source:
--   - generalization: T = 3m⌈log² n⌉ with m = A_t n² → the mean and the tail bound for every T ∈ ℕ and every integer m ≥ 2; reason: they hold for every T and m ≥ 2; the paper's T and m are instances
--   - reading: J ∼ Bin(T, 1/m) → the binomial probabilities C(T,k) m^{−k} (1 − 1/m)^{T−k} written out, J > 2T/m as 2T < km; reason: the law of J stated on the page
--   - reading: log² n, base not printed → (log_β n)² for an arbitrary base β > 1; reason: covers every reading of the base
--   - reading: e^{−Ω(log² n)} → ∃ c > 0 with (e/4)^{T/m} ≤ e^{−c log² n} for all m ≥ 2 and n; reason: the meaning of Ω; c is uniform in m and n
-- source:
--   Dujmovic–Haferkamp–Poremba, On the pseudorandomness of simple quantum processes, arXiv:2610.02100 (held version sha256 9920ec45…), proof of Theorem 1.3, Eq. (19), p.15

import Mathlib
import Definitions.Def_QuantumHMMR_logSq

namespace QuantumHMMR

/-- **Eq. (19)** (Dujmovic–Haferkamp–Poremba, *On the pseudorandomness of simple quantum processes*, arXiv:2610.02100 (held version, sha256 9920ec45…4f20), proof of Theorem 1.3, p.15). Let `J` be the number of insertions among the
`T` updates; since the updates are independent and each is an insertion with probability `1/m`,
`J ∼ Bin(T, 1/m)`. Then `E[J] = T/m`, and the Chernoff bound gives
`Pr[J > 2T/m] ≤ (e/4)^{T/m}`; at `T = 3m⌈log² n⌉` this is `e^{-Ω(log² n)}`.

**Formalization Note** The law of `J` is written out: `Pr[J = k] = C(T, k) m^{-k} (1 - 1/m)^{T-k}`,
and `J > 2T/m` is `2T < k m`. The first part is stated for every `T` and every integer `m ≥ 2` (the
range of `m` on p.11). In the second part `log² n = (log_β n)²` for an arbitrary base `β > 1`, and
`Ω` is one constant `c > 0`, uniform in `m` and `n`. -/
theorem eq_19 :
    (∀ m T : ℕ, 2 ≤ m →
      ∑ k ∈ Finset.range (T + 1),
          (k : ℝ) * (T.choose k : ℝ) * ((m : ℝ)⁻¹) ^ k * (1 - (m : ℝ)⁻¹) ^ (T - k) = T / m ∧
      ∑ k ∈ (Finset.range (T + 1)).filter (fun k => 2 * T < k * m),
          (T.choose k : ℝ) * ((m : ℝ)⁻¹) ^ k * (1 - (m : ℝ)⁻¹) ^ (T - k)
        ≤ (Real.exp 1 / 4) ^ ((T : ℝ) / m)) ∧
    ∀ β : ℝ, 1 < β → ∃ c : ℝ, 0 < c ∧ ∀ m n : ℕ, 2 ≤ m →
      (Real.exp 1 / 4) ^ (((3 * m * ⌈logSq β n⌉₊ : ℕ) : ℝ) / m) ≤ Real.exp (-(c * logSq β n)) := by sorry

end QuantumHMMR
