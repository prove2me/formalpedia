-- Prove2me | Theorems.Thm_PermutationStreams_Parity_Supplement_theorem_1_2
-- name    : PermutationStreams.Parity.Supplement.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:57:21.574227+00:00
-- url     : https://prove2.me/theorems/fd1f9cd7-0fdc-4b4f-876e-71ceee2c0df0
-- title:
--   Theorem 1.2 — pattern dichotomy: $S_\sigma(n)=\Theta_\sigma(\log n)$ or $\Theta_\sigma(n)$
-- statement:
--   Let $\sigma\in S_k$ be a fixed pattern of length $k\ge2$, and let $S_\sigma(n)$ be the minimum number of bits of a deterministic one-pass streaming algorithm detecting $\sigma$ in permutations of $[n]$. Then
--
--   $$
--   S_\sigma(n)=\begin{cases}\Theta_\sigma(\log n), & \text{if }\sigma\text{ is monotone or }|\sigma|=3,\\ \Theta_\sigma(n), & \text{otherwise.}\end{cases}
--   $$
--
--   Explicitly: in the first case there are $c,C>0$ and $n_0$, depending only on $\sigma$, with $c\log_2n\le S_\sigma(n)\le C\log_2 n$ for all $n\ge n_0$; in the second case there are such constants with $c\,n\le S_\sigma(n)\le C\,n$ for all $n\ge n_0$.
--
--   The theorem completes the classification of the one-pass space complexity of fixed permutation patterns; the lower bounds are due to Berendsohn and the linear upper bound rests on the Marcus–Tardos theorem, both cited in the paper and part of what a proof must establish.
--
--   Differences from the source:
--   - encoding: positions and values in [n] = {1,…,n}, π ∈ S_n → Equiv.Perm (Fin n), with position i and value π i read as i + 1 and π i + 1; reason: every formula is evaluated on the shifted 1-based values; same instances
--   - reading: 'a one-pass algorithm' in the definition of S_σ(n) → a deterministic clock-free one-pass algorithm with space ⌈log₂ #states⌉; reason: the abstract and §1.2 say the patterns are detected deterministically, Corollary 5.8 speaks of deterministic space complexity, and every §6 bound is a state count
--   - encoding: Θ_σ(log n), Θ_σ(n) → ∃ c C > 0, ∃ n₀, ∀ n ≥ n₀, c·f(n) ≤ S_σ(n) ≤ C·f(n), with f(n) = log₂ n or n; reason: the constants and threshold are quantified after σ and before n, so they depend on σ only
--   - encoding: σ monotone (increasing or decreasing) → σ = 1 ∨ σ = Fin.revPerm; reason: identity and reversal of [k]; same patterns
-- source:
--   Mark Braverman, Or Zamir, STOC 2027 submission #74 (October 2026), Parity and Pattern Detection in Permutation Streams, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/74.pdf (SHA-256 3f0b683e25232855e98d1caa358e35f2670633688d8a799e4d01a207aa5600ea), §1.2 p. 2, Theorem 1.2; proof §6.2 p. 14 (with Theorem 6.2 and Theorem 6.4, p. 14)

import Definitions.Def_PermutationStreams_Parity_Supplement_Patterns

namespace PermutationStreams.Parity.Supplement

/-- Braverman–Zamir, STOC 2027 submission #74, Theorem 1.2 (pattern dichotomy), p.2. For every
pattern `σ ∈ S_k` with `k ≥ 2`: if `σ` is monotone or `k = 3` then `S_σ(n) = Θ_σ(log n)`, and
otherwise `S_σ(n) = Θ_σ(n)`. The constants `c, C > 0` and the threshold `n₀` depend on `σ` only. -/
theorem theorem_1_2 (k : ℕ) (hk : 2 ≤ k) (σ : Equiv.Perm (Fin k)) :
    ((IsMonotonePattern σ ∨ k = 3) →
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
        c * Real.logb 2 n ≤ (spaceComplexity σ n : ℝ) ∧
        (spaceComplexity σ n : ℝ) ≤ C * Real.logb 2 n) ∧
    (¬ (IsMonotonePattern σ ∨ k = 3) →
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
        c * (n : ℝ) ≤ (spaceComplexity σ n : ℝ) ∧
        (spaceComplexity σ n : ℝ) ≤ C * (n : ℝ)) := by sorry

end PermutationStreams.Parity.Supplement
