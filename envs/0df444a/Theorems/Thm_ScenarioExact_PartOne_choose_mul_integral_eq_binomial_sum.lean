-- Prove2me | Theorems.Thm_ScenarioExact_PartOne_choose_mul_integral_eq_binomial_sum
-- name    : ScenarioExact.PartOne.choose_mul_integral_eq_binomial_sum
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T19:00:55.184004+00:00
-- url     : https://prove2.me/theorems/8582bd15-fd28-4a54-a6aa-5c255314d5f3
-- title:
--   §3, PART 1, p. 9 — $\binom Nd\int_\varepsilon^1(1-\alpha)^{N-d}d\alpha^{d-1}\mathrm d\alpha=\sum_{i=0}^{d-1}\binom Ni\varepsilon^i(1-\varepsilon)^{N-i}$
-- statement:
--   Let $d$ and $N$ be integers with $1\le d\le N$ and let $\varepsilon\in[0,1]$. Then
--   $$\binom Nd\int_\varepsilon^1(1-\alpha)^{N-d}\,d\,\alpha^{d-1}\,\mathrm d\alpha=\sum_{i=0}^{d-1}\binom Ni\varepsilon^i(1-\varepsilon)^{N-i}.$$
--
--   This is the last part of PART 1 of the proof of Theorem 2.4: with $F(\mathrm d\alpha)=d\,\alpha^{d-1}\mathrm d\alpha$ from (3.2), it turns $\binom Nd\int_\varepsilon^1(1-\alpha)^{N-d}F(\mathrm d\alpha)$ into the binomial tail of (2.3). The left side is a regularised incomplete beta integral; a related upper-tail identity is on the platform as `binomial_upper_tail_eq_incomplete_beta`.
--
--   **Formalization Note.** The factor $d$ in the paper's "$\mathrm d\alpha^{d-1}\mathrm d\alpha$" is the dimension $d$ multiplying $\alpha^{d-1}$ (the density of the distribution $\alpha^d$), written `(d : ℝ) * α ^ (d - 1)`. The integral is the interval (Lebesgue) integral over $[\varepsilon,1]$ of a continuous function.
-- source:
--   Campi & Garatti, The exact feasibility of randomized solutions of uncertain convex programs, SIAM J. Optim. 19(3) (2008); authors' final manuscript, p. 9, §3, PART 1, display from '[since F(dα) = dα^{d−1} dα]' to the final sum

import Mathlib

namespace ScenarioExact.PartOne

/-- §3, PART 1, p. 9 (integration by parts): for `1 ≤ d ≤ N` and `ε ∈ [0, 1]`,
`binom(N, d) ∫_ε^1 (1 − α)^{N−d} d α^{d−1} dα = ∑_{i=0}^{d−1} binom(N, i) ε^i (1 − ε)^{N−i}`. -/
theorem choose_mul_integral_eq_binomial_sum {d N : ℕ} (hd : 1 ≤ d) (hN : d ≤ N) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (N.choose d : ℝ) * ∫ α in ε..1, (1 - α) ^ (N - d) * ((d : ℝ) * α ^ (d - 1)) =
      ∑ i ∈ Finset.range d, (N.choose i : ℝ) * ε ^ i * (1 - ε) ^ (N - i) := by sorry

end ScenarioExact.PartOne
