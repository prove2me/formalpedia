-- Prove2me | Theorems.Thm_PermutationStreams_Parity_streaming_space_lower_bound
-- name    : PermutationStreams.Parity.streaming_space_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:59:34.870204+00:00
-- url     : https://prove2.me/theorems/5091c14f-a645-419f-9982-262458c94c26
-- title:
--   Theorem 1.1 — randomized space lower bounds for permutation parity
-- statement:
--   A randomized $p$-pass streaming algorithm reads a permutation $\pi$ of $[n]$ as the stream $\pi_1,\dots,\pi_n$, $p$ times forwards, keeping an $s$-bit memory state between values and between passes, and outputs a sign. It computes the sign with error at most $1/3$ when, for **every** permutation $\pi$, the probability over its random coins that the output differs from $\operatorname{sgn}(\pi)=(-1)^{\operatorname{inv}(\pi)}$ is at most $1/3$.
--
--   **Theorem 1.1 (Permutation parity).** Any such one-pass algorithm requires $\Omega(n)$ bits of space; more generally a $p$-pass algorithm requires $\Omega(n/p)$ bits. Explicitly, there is an absolute constant $\alpha>0$ such that:
--
--   1. for all $n$, all $p\ge1$ and all $s$, every randomized $p$-pass algorithm with $s$ bits of memory computing the sign with error at most $1/3$ satisfies
--
--   $$
--   (3p-1)\,s+1\ \ge\ \alpha\left\lfloor\frac n3\right\rfloor-\log_2 3 ;
--   $$
--
--   2. there are absolute constants $c>0$ and $n_0$ such that every such algorithm satisfies $s\ge c\,n/p$ whenever $n\ge n_0$, for every $p\ge1$.
--
--   For $p=1$ the first clause reads $2s+1\ge\alpha\lfloor n/3\rfloor-\log_2 3$, and the second gives $s=\Omega(n)$. The bound is tight for one pass: a deterministic algorithm with $n+1$ bits computes the sign. The constants do not depend on $n$, $p$, $s$ or the algorithm.
--
--   **Formalization Note** The model allows transitions to depend on the publicly known pass and position, and represents randomness as a finite probability space of deterministic machines on a common state set $S$ with $|S|\le2^s$ (see the streaming definition). All arithmetic is real; $\lfloor n/3\rfloor$ is natural-number division.
--
--   Differences from the source:
--   - generalization: Ω(n) and Ω(n/p) bits → additionally the explicit inequality (3p−1)s+1 ≥ α⌊n/3⌋ − log₂3 with an absolute α > 0, for all n and p ≥ 1; reason: it is the inequality derived in the source's proof on p. 8; the source's Ω claims are the second clause
--   - encoding: s = Ω(n/p) for all sufficiently large n → ∃ c > 0, n₀ with c·n/p ≤ s for all n ≥ n₀ and all p ≥ 1; reason: the meaning of the Ω claim with constants independent of p and of the algorithm
--   - generalization: streaming algorithms whose transitions see the state and the arriving value → transitions may also see the public clock (pass, position); reason: enlarges the class of algorithms; every source algorithm ignores the clock
--   - encoding: randomized algorithm, s bits of space → finite probability space of deterministic machines on a common state set S with |S| ≤ 2^s; reason: every randomized s-bit algorithm induces such a mixture with the same output law on each input (see the streaming definition)
--   - encoding: a permutation of [n] with sign ±1 → Equiv.Perm (Fin n) with sgn a unit of ℤ; reason: an order-preserving shift by one changes no inversion
-- source:
--   Mark Braverman, Or Zamir, STOC 2027 submission #74 (October 2026), Parity and Pattern Detection in Permutation Streams, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/74.pdf (SHA-256 3f0b683e25232855e98d1caa358e35f2670633688d8a799e4d01a207aa5600ea), §1.1, p. 2, Theorem 1.1; proof §4.3, p. 8 (finite inequality (3p − 1)s + 1 ≥ αm − log 3 with m = ⌊n/3⌋)

import Definitions.Def_PermutationStreams_Parity_StreamingAlgorithm

namespace PermutationStreams.Parity

/-- Braverman–Zamir, Theorem 1.1 (Permutation parity), p.2; proof §4.3, p.8.
There is an absolute constant `α > 0` such that every randomized `p`-pass streaming algorithm
(`p ≥ 1`) with an `s`-bit state set that computes the sign of every permutation of `[n]` with
error at most `1/3` satisfies `(3p - 1)s + 1 ≥ α⌊n/3⌋ - log₂ 3`; and there are absolute
`c > 0` and `n₀` with `s ≥ c·n/p` for all `n ≥ n₀` and all `p ≥ 1` (so `s = Ω(n)` for one
pass and `s = Ω(n/p)` for `p` passes). -/
theorem streaming_space_lower_bound :
    ∃ α : ℝ, 0 < α ∧
      (∀ (n p s : ℕ), 1 ≤ p →
        ∀ {S Ω : Type} [Fintype S] [Fintype Ω] (A : RandStreamAlg n p S Ω),
          Fintype.card S ≤ 2 ^ s → A.ComputesSignWithError (1 / 3) →
          α * ((n / 3 : ℕ) : ℝ) - Real.logb 2 3 ≤ (3 * (p : ℝ) - 1) * s + 1) ∧
      ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ (n p s : ℕ), n₀ ≤ n → 1 ≤ p →
        ∀ {S Ω : Type} [Fintype S] [Fintype Ω] (A : RandStreamAlg n p S Ω),
          Fintype.card S ≤ 2 ^ s → A.ComputesSignWithError (1 / 3) →
          c * n / p ≤ (s : ℝ) := by sorry

end PermutationStreams.Parity
