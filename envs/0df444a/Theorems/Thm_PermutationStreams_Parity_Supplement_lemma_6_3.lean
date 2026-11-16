-- Prove2me | Theorems.Thm_PermutationStreams_Parity_Supplement_lemma_6_3
-- name    : PermutationStreams.Parity.Supplement.lemma_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:56:42.585336+00:00
-- url     : https://prove2.me/theorems/822c4907-46ec-441d-a7b0-87d7a8a2c879
-- title:
--   Lemma 6.3 — a $1+(1+C_\sigma)^n$-state detector for every fixed pattern
-- statement:
--   Let $\sigma\in S_k$ be a pattern and let $C\ge1$ be a real constant with $|\mathrm{Av}_t(\sigma)|\le C^t$ for every integer $t\ge0$, where $\mathrm{Av}_t(\sigma)$ is the set of permutations of $[t]$ avoiding $\sigma$ (Theorem 6.2, of Marcus and Tardos, provides such a constant $C_\sigma$). Then for every $n$ there is a deterministic one-pass streaming algorithm detecting $\sigma$ in permutations of $[n]$ with at most
--
--   $$
--   1+(1+C)^n
--   $$
--
--   states. In particular it uses at most $\lceil n\log_2(1+C)\rceil+1$ bits, which is $O_\sigma(n)$.
--
--   This gives the linear upper bound in the second case of the pattern dichotomy.
--
--   Differences from the source:
--   - encoding: positions and values in [n] = {1,…,n}, π ∈ S_n → Equiv.Perm (Fin n), with position i and value π i read as i + 1 and π i + 1; reason: every formula is evaluated on the shifted 1-based values; same instances
--   - encoding: 'a deterministic one-pass streaming algorithm … with at most … states' → a clock-free OnePassAlg n S Bool with Fintype.card S ≤ 1 + (1 + C)^n, required correct only on permutations of [n]; reason: the paper's automaton (states q_w, q_yes) sees only the state and the arriving value, and bits are the logarithm of the state count
--   - reading: C_σ, the constant of Theorem 6.2 → every real C ≥ 1 with |Av_t(σ)| ≤ C^t for all t ≥ 0; reason: Theorem 6.2 only asserts that such a constant exists and the lemma uses nothing else about it
--   - generalization: it uses O_σ(n) bits → it uses at most ⌈n·log₂(1 + C)⌉ + 1 bits; reason: the explicit bound is what the lemma's proof gives by taking the logarithm of the state count, and it implies O_σ(n) with the σ-dependent constant log₂(1 + C) + 2
-- source:
--   Mark Braverman, Or Zamir, STOC 2027 submission #74 (October 2026), Parity and Pattern Detection in Permutation Streams, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/74.pdf (SHA-256 3f0b683e25232855e98d1caa358e35f2670633688d8a799e4d01a207aa5600ea), §6.1 p. 14, Lemma 6.3 (with Theorem 6.2, p. 14)

import Definitions.Def_PermutationStreams_Parity_Supplement_Patterns

namespace PermutationStreams.Parity.Supplement

open PatternRangeCounting1593.RangeCounting

/-- Braverman–Zamir, STOC 2027 submission #74, Lemma 6.3, p.14, for the constant of Theorem 6.2:
for every pattern `σ ∈ S_k` and every real `C ≥ 1` with `|Av_t(σ)| ≤ C^t` for all `t ≥ 0`, and every
`n`, some deterministic clock-free one-pass algorithm detects `σ` in permutations of `[n]` with at
most `1 + (1 + C)^n` states; in particular it uses at most `⌈n log₂(1 + C)⌉ + 1 = O_σ(n)` bits. -/
theorem lemma_6_3 {k : ℕ} (σ : Equiv.Perm (Fin k)) (C : ℝ) (hC : 1 ≤ C)
    (hAv : ∀ t : ℕ, ((Av t σ).card : ℝ) ≤ C ^ t) (n : ℕ) :
    ∃ (S : Type) (_ : Fintype S) (A : OnePassAlg n S Bool),
      A.Detects σ ∧ (Fintype.card S : ℝ) ≤ 1 + (1 + C) ^ n ∧
      A.UsesBits (⌈(n : ℝ) * Real.logb 2 (1 + C)⌉₊ + 1) := by sorry

end PermutationStreams.Parity.Supplement
