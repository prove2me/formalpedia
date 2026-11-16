-- Prove2me | Theorems.Thm_PermutationStreams_Parity_Supplement_lemma_5_1
-- name    : PermutationStreams.Parity.Supplement.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:54:42.119824+00:00
-- url     : https://prove2.me/theorems/d64087a6-0b97-44e9-b071-d77a6616d756
-- title:
--   Lemma 5.1 — weighted inversion identity and its one-pass computation
-- statement:
--   Let $\pi\in S_n$ and let $W(\pi)=\sum_{i<j,\ \pi_i>\pi_j}(\pi_i-\pi_j)$ be its weighted inversion number, $Q(n)=\sum_{v=1}^n v^2$.
--
--   1. For every $n$ and every $\pi\in S_n$,
--   $$
--   W(\pi)=Q(n)-\sum_{i=1}^n i\,\pi_i .
--   $$
--   2. There is a constant $C>0$ such that for every $n\ge2$ some deterministic one-pass streaming algorithm (whose transitions see only the current state and value) with at most $2^s$ states, $s\le C\log_2 n$, outputs $W(\pi)$ on every permutation $\pi$ of $[n]$.
--
--   The identity turns a quadratic sum over pairs into a linear sum over positions, which a streaming algorithm can accumulate; it is the arithmetic core of both length-three detectors.
--
--   Differences from the source:
--   - encoding: positions and values in [n] = {1,…,n}, π ∈ S_n → Equiv.Perm (Fin n), with position i and value π i read as i + 1 and π i + 1; reason: every formula is evaluated on the shifted 1-based values; same instances
--   - encoding: 'computed deterministically in one pass with O(log n) bits' → a clock-free OnePassAlg n S ℤ with |S| ≤ 2^s, correct on every permutation of [n]; reason: the paper's register algorithm counts its position in its own memory; bits are measured by the state count
--   - encoding: O(log n) bits → ∃ C > 0, ∀ n ≥ 2, s ≤ C·log₂ n; reason: log₂ n ≥ 1 for n ≥ 2, so a bound eventually in n is equivalent to one for all n ≥ 2 after enlarging C; n = 1 is excluded because log₂ 1 = 0
-- source:
--   Mark Braverman, Or Zamir, STOC 2027 submission #74 (October 2026), Parity and Pattern Detection in Permutation Streams, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/74.pdf (SHA-256 3f0b683e25232855e98d1caa358e35f2670633688d8a799e4d01a207aa5600ea), §5.1 p. 9, Lemma 5.1

import Definitions.Def_PermutationStreams_Parity_Supplement_OnePass
import Definitions.Def_PermutationStreams_Parity_Supplement_Statistics

namespace PermutationStreams.Parity.Supplement

/-- Braverman–Zamir, STOC 2027 submission #74, Lemma 5.1, p.9. (1) For every permutation `π` of
`[n]`, `W(π) = Q(n) − ∑_{i=1}^n i·π_i` (1-based positions and values). (2) `W(π)` is computed by a
deterministic clock-free one-pass algorithm with `O(log n)` bits: one constant `C` serves every
`n ≥ 2`. -/
theorem lemma_5_1 :
    (∀ (n : ℕ) (π : Equiv.Perm (Fin n)),
      W π = Q n - ∑ i : Fin n, ((i : ℤ) + 1) * val π i) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      ∃ (S : Type) (_ : Fintype S) (A : OnePassAlg n S ℤ) (s : ℕ),
        (∀ π : Equiv.Perm (Fin n), A.run π = W π) ∧ A.UsesBits s ∧
        (s : ℝ) ≤ C * Real.logb 2 n := by sorry

end PermutationStreams.Parity.Supplement
