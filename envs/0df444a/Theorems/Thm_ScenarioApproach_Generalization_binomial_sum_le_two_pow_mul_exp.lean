-- Prove2me | Theorems.Thm_ScenarioApproach_Generalization_binomial_sum_le_two_pow_mul_exp
-- name    : ScenarioApproach.Generalization.binomial_sum_le_two_pow_mul_exp
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-30T17:32:55.799253+00:00
-- url     : https://prove2.me/theorems/07107728-58e2-47a2-855a-308540de4afd
-- title:
--   Eq. (3.9) — explicit exponential bound on the binomial tail
-- statement:
--   Let $N\ge 0$ and $d\ge 1$ be integers and let $\varepsilon\in[0,1]$. Then
--
--   $$
--   \sum_{i=0}^{d-1}\binom{N}{i}\varepsilon^i(1-\varepsilon)^{N-i}\;\le\;2^{d-1}\Big(1-\frac{\varepsilon}{2}\Big)^N\;\le\;2^{d-1}\exp\Big(-\frac{\varepsilon}{2}N\Big).
--   $$
--
--   The left-hand side is the right-hand side of the generalization bound (3.4) of Theorem 3.7. This elementary estimate turns the implicit sample-size condition (3.8), $\sum_{i=0}^{d-1}\binom{N}{i}\varepsilon^i(1-\varepsilon)^{N-i}\le\beta$, into the explicit sufficient condition $N\ge\frac{2}{\varepsilon}\big(\ln\frac1\beta+(d-1)\ln2\big)$, from which Theorem 1.3 follows.
--
--   **Formalization Note** $N-i$ is natural-number subtraction; terms with $i>N$ have $\binom Ni=0$, so the truncation never matters. $2^{d-1}$ is taken with $d\ge1$. The statement records the two inequalities at the end of the chain (3.9) as a conjunction.
-- source:
--   Campi & Garatti, Introduction to the Scenario Approach, SIAM/MOS 2018, DOI 10.1137/1.9781611975444, p. 41, Eq. (3.9)

import Mathlib

namespace ScenarioApproach.Generalization

/-- Eq. (3.9) (p. 41): for `d ≥ 1` and `ε ∈ [0, 1]`,
`∑_{i=0}^{d-1} (N choose i) ε^i (1-ε)^{N-i} ≤ 2^{d-1} (1 - ε/2)^N ≤ 2^{d-1} exp(-(ε/2) N)`. -/
theorem binomial_sum_le_two_pow_mul_exp (N d : ℕ) (hd : 1 ≤ d) (ε : ℝ) (hε0 : 0 ≤ ε)
    (hε1 : ε ≤ 1) :
    ∑ i ∈ Finset.range d, (N.choose i : ℝ) * ε ^ i * (1 - ε) ^ (N - i) ≤
        2 ^ (d - 1) * (1 - ε / 2) ^ N ∧
      2 ^ (d - 1) * (1 - ε / 2) ^ N ≤ 2 ^ (d - 1) * Real.exp (-(ε / 2) * N) := by sorry

end ScenarioApproach.Generalization
