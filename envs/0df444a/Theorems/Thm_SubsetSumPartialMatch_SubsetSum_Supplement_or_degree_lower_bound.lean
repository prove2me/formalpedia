-- Prove2me | Theorems.Thm_SubsetSumPartialMatch_SubsetSum_Supplement_or_degree_lower_bound
-- name    : SubsetSumPartialMatch.SubsetSum.Supplement.or_degree_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:14:48.211312+00:00
-- url     : https://prove2.me/theorems/3750f6d7-06aa-41ea-9f3d-c57691fb419b
-- title:
--   Theorem 3.10 (companion theorem; not used in the proof of the goal) — OR-circuit degree barrier
-- statement:
--   Let $l,r\ge0$ be real numbers. For each natural length $n$, let $P_{n,1/2}$ have rows indexed by all binary strings of length $n$ and columns indexed by queries over $\{0,1,*\}$ with exactly $\lfloor n/2\rfloor$ specified positions. Its entry is one precisely when the binary string agrees with the query at every specified position.
--
--   An OR circuit has an arbitrary finite set of middle gates and two matrices $L_C,R_C$ with coefficients in $\{0,1\}$. It computes $P_{n,1/2}$ when the integer product $L_C R_C$ is nonzero exactly at the one entries of $P_{n,1/2}$; different middle gates may cover the same entry. Write $\deg_L(C)$ for the maximum row support of $L_C$ and $\deg_R(C)$ for the maximum column support of $R_C$.
--
--   Suppose that for every real $\varepsilon>0$ there is a natural threshold $N$ such that, for every natural $n\ge N$, there exists one OR circuit $C$ computing $P_{n,1/2}$ and satisfying both
--   $$
--   \deg_L(C)\le2^{(l+\varepsilon)n},\qquad
--   \deg_R(C)\le2^{(r+\varepsilon)n}.
--   $$
--   Then
--   $$
--   l+r\ge\frac12.
--   $$
--   This companion theorem establishes the OR-circuit degree barrier for these matrices. It is independent of the proof of the mission's subset-sum goal. No constructibility, color, width, symmetry or bound on the number of middle gates is imposed.
--
--   **Formalization Note** The circuit container, matrix and degrees are the published definitions. The new predicate imposes binary entries and support equality over the integers. Natural degrees are cast to real numbers, and powers have positive real base two. Both bounds constrain the same existential circuit. All natural lengths, including odd lengths, occur in the eventual hypothesis.
--
--   Differences from the source:
--   - encoding: binary and query strings on n coordinates, with floor(n/2) specified positions → published BinStr n and PMCol n (1/2), using Fin n, Bool and Option Bool; reason: the published carriers relabel the same strings and use the source floor convention from p. 16
--   - encoding: one OR-circuit family with simultaneous degree bounds 2^((l+o(1))*n) and 2^((r+o(1))*n) → for every positive real epsilon there is N such that every natural n >= N admits one circuit satisfying both epsilon-slack degree bounds; reason: the eventual-slack formulation on p. 16 is equivalent to the two asymptotic rates; a diagonal choice gives one family and finitely many lengths admit trivial OR circuits
-- source:
--   Li & Ye, Subset Sum via Partial Match, STOC 2027 submission #24, preprint, source.pdf sha256 e5f396c346fb73c14219a019a35c9a16b1adc4b4b84978d3658736d31958ae5c, p. 27, Theorem 3.10; proof pp. 27–28; conventions pp. 15–16.

import Mathlib
import Definitions.Def_SubsetSumPartialMatch_SubsetSum_Supplement_ComputesOR

namespace SubsetSumPartialMatch.SubsetSum.Supplement

/-- Theorem 3.10 (p. 27, proof pp. 27–28). Nonuniform OR circuits for the half-specified
partial-match matrices cannot have degree exponents whose sum is below 1/2.
The two exponent bounds hold simultaneously, eventually at every natural length, for
each positive slack; the finite middle type is unrestricted and may depend on the length.
This is a companion theorem, independent of the proof of Theorem 4.1. -/
theorem or_degree_lower_bound (l r : ℝ) (hl : 0 ≤ l) (hr : 0 ≤ r)
    (hcircuits : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ C : LinCircuit (BinStr n) (PMCol n (1 / 2 : ℝ)),
        ComputesOR C (pm n (1 / 2 : ℝ)) ∧
        (C.degL : ℝ) ≤ (2 : ℝ) ^ ((l + ε) * (n : ℝ)) ∧
        (C.degR : ℝ) ≤ (2 : ℝ) ^ ((r + ε) * (n : ℝ))) :
    1 / 2 ≤ l + r := by sorry

end SubsetSumPartialMatch.SubsetSum.Supplement
