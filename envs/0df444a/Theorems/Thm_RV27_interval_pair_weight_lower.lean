-- Prove2me | Theorems.Thm_RV27_interval_pair_weight_lower
-- name    : RV27.interval_pair_weight_lower
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-06T15:07:05.752426+00:00
-- url     : https://prove2.me/theorems/28accd29-3156-4777-86a5-ceb5f2add710
-- title:
--   Riesel–Vaughan lower bound for the singular-series-weighted pair sum over primes in an interval
-- statement:
--   Let $S$ be a finite set of odd primes and $\mathcal T$ a set of primes in an interval $[M, M+N)$, none of them in $S$ and all larger than $Q$, where $Q \ge 21$ is an integer with $16Q^2 \le N$. Let $w \ge 1$ with $12w \le Q$. For $n \ge 1$ put
--   $$w_S(n) = \prod_{p \in S,\ p \mid n} \frac{p-2}{p-1}$$
--   (the Riesel–Vaughan weight $\prod_{p\mid n,\,p>2}(p-2)/(p-1)$ truncated to $S$). Then, with $T = |\mathcal T|$,
--   $$\sum_{t, t' \in \mathcal T} w_S(t + t') \ \ge\ \mathcal P_S \Big( \frac{16}{15} T^2 - \frac{N T}{15(\log Q - \log 20)} - \Big(\frac{N}{w} + 2\Big) B_S\, T \Big),$$
--   where $\mathcal P_S = \prod_{p\in S}\big(1 - (p-1)^{-2}\big)$ and $B_S = \prod_{p \in S}\big(1 + \frac{p-1}{p(p-2)}\big)$.
--
--   This is the content of Riesel–Vaughan §8 (Lemmas 10–13) for a single interval $I_k$: expanding $w_S$ over odd squarefree $d$ and Dirichlet characters, grouping characters by conductor $q$ gives exactly $\mathcal P_S \sum_q \mu(q) f(q) \sum^*_{\chi \bmod q} \chi(-1)|S(\chi)|^2$ with $f(q) = \prod_{p\mid q} \frac{1}{p(p-2)}$; the conductors $q \le w$ are controlled by the Montgomery–Vaughan weighted large sieve (constant $16$), where the extremal modulus is $q = 5$ and the single primitive character mod $3$ is odd, and the conductors $q > w$ contribute at most $(N/w + 2) B_S T$.
-- source:
--   H. Riesel and R. C. Vaughan, On sums of primes, Ark. Mat. 21 (1983) 45–74, §8, equations (8.1)–(8.18) and Lemmas 10–13 (with the weight truncated to the primes of S, which removes their terms Ξ_k and Δ_k); H. L. Montgomery and R. C. Vaughan, The large sieve, Mathematika 20 (1973) 119–134, Lemmas 3 and 8. Uses platform nodes MVSieve.primitive_character_large_sieve and MVSieve.large_sieve_weight_lower.

import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem RV27.interval_pair_weight_lower (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2)
    (Q : ℕ+) (M N w : ℕ) (hN : 16 * (Q : ℕ) ^ 2 ≤ N) (hw : 1 ≤ w) (hwQ : 12 * w ≤ (Q : ℕ))
    (hQ20 : 20 < (Q : ℕ)) (T : Finset ℕ) (hTI : T ⊆ Finset.Ico M (M + N))
    (hTp : ∀ t ∈ T, t.Prime ∧ (Q : ℕ) < t) (hTS : ∀ t ∈ T, ∀ p ∈ S, ¬ p ∣ t) :
    (∏ p ∈ S, (1 - 1 / ((p : ℝ) - 1) ^ 2)) *
      ((16 / 15) * (T.card : ℝ) ^ 2 - (N : ℝ) * T.card / (15 * (Real.log Q - Real.log 20)) -
        ((N : ℝ) / w + 2) * (∏ p ∈ S, (1 + ((p : ℝ) - 1) / ((p : ℝ) * ((p : ℝ) - 2)))) * T.card) ≤
    ∑ t ∈ T, ∑ t' ∈ T, ∏ p ∈ S,
      (if p ∣ t + t' then ((p : ℝ) - 2) / ((p : ℝ) - 1) else 1) := by sorry
