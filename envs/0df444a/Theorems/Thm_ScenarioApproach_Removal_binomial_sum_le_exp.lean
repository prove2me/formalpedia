-- Prove2me | Theorems.Thm_ScenarioApproach_Removal_binomial_sum_le_exp
-- name    : ScenarioApproach.Removal.binomial_sum_le_exp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T05:39:47.876689+00:00
-- url     : https://prove2.me/theorems/3c352328-2b84-4c20-a39e-751c39680cbb
-- title:
--   Eqs. (3.15)–(3.16) — exponential bound on $\sum_{i=0}^{k+d-1}\binom Ni\varepsilon_k^i(1-\varepsilon_k)^{N-i}$
-- statement:
--   Let $k \ge 1$, $d \ge 1$ and $N$ be natural numbers, let $a = 1 + 1/\sqrt k$, and let $\varepsilon_k \in [0,1]$. Then
--
--   $$
--   \sum_{i=0}^{k+d-1} \binom Ni \varepsilon_k^i (1-\varepsilon_k)^{N-i} \le a^{k+d-1}\left(1 - \left(1 - \frac1a\right)\varepsilon_k\right)^N
--   $$
--
--   (the last line of (3.15)), and
--
--   $$
--   \sum_{i=0}^{k+d-1} \binom Ni \varepsilon_k^i (1-\varepsilon_k)^{N-i} \le \exp\bigl(-(1-a)(k+d-1)\bigr) \cdot \exp\left(-\left(1-\frac1a\right)\varepsilon_k N\right). \qquad (3.16)
--   $$
--
--   These bounds turn the binomial tail in (3.13) into an explicit exponential, from which the violation level $\varepsilon_k$ of Theorem 1.2 is solved for.
--
--   **Formalization Note** The book applies the chain to the specific $\varepsilon_k$ of (1.9); the inequalities hold for every $\varepsilon_k \in [0,1]$, and that range is stated as a hypothesis (for $\varepsilon_k > 1$ the factors $(1-\varepsilon_k)^{N-i}$ change sign and the chain breaks). The exponent $k+d-1$ is a natural number, exact because $d \ge 1$; terms with $i > N$ vanish since $\binom Ni = 0$.
-- source:
--   Campi & Garatti, Introduction to the Scenario Approach, SIAM/MOS 2018, DOI 10.1137/1.9781611975444, p. 47, Eqs. (3.15)–(3.16)

import Mathlib

namespace ScenarioApproach.Removal

theorem binomial_sum_le_exp (N k d : ℕ) (hk : 1 ≤ k) (hd : 1 ≤ d)
    (a : ℝ) (ha : a = 1 + 1 / Real.sqrt k)
    (εk : ℝ) (hε0 : 0 ≤ εk) (hε1 : εk ≤ 1) :
    (∑ i ∈ Finset.range (k + d), (N.choose i : ℝ) * εk ^ i * (1 - εk) ^ (N - i) ≤
        a ^ (k + d - 1) * (1 - (1 - 1 / a) * εk) ^ N) ∧
      (∑ i ∈ Finset.range (k + d), (N.choose i : ℝ) * εk ^ i * (1 - εk) ^ (N - i) ≤
        Real.exp (-(1 - a) * ((k + d - 1 : ℕ) : ℝ)) * Real.exp (-(1 - 1 / a) * εk * N)) := by sorry

end ScenarioApproach.Removal
