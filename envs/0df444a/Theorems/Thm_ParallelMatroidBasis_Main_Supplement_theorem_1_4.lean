-- Prove2me | Theorems.Thm_ParallelMatroidBasis_Main_Supplement_theorem_1_4
-- name    : ParallelMatroidBasis.Main.Supplement.theorem_1_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:02:57.760653+00:00
-- url     : https://prove2.me/theorems/044a1797-e56e-470c-8543-07144d898695
-- title:
--   Theorem 1.4 — matroid intersection in $\tilde O(n^{7/9})$ rounds of polynomially many independence queries, with high probability
-- statement:
--   There is an exponent $k\in\mathbb N$ such that for every $c>0$ there are constants $C>0$, $d\in\mathbb N$ and one randomized parallel algorithm $A$ — one procedure for every ground-set size $n$, seeing two matroids $M_1=(E,\mathcal I_1)$, $M_2=(E,\mathcal I_2)$ on the ground set $E=[n]$ only through independence queries to each of them — such that for all $n$ and all such $M_1,M_2$:
--
--   1. every run uses at most $C\,(1+n^{7/9}(\log_2(n+2))^k)$ adaptive rounds;
--   2. every round asks at most $(n+1)^d$ queries (to the two oracles together);
--   3. if $n\ge1$, with probability at least $1-n^{-c}$ the output $S$ solves the matroid intersection problem:
--   $$S\in\mathcal I_1\cap\mathcal I_2\quad\text{and}\quad |S|=\max_{T\in\mathcal I_1\cap\mathcal I_2}|T| .$$
--
--   This improves the previous $\tilde O(n^{17/21})$-round independence-query algorithm of [KPS25, KPS26] for exact matroid intersection.
--
--   **Formalization Note** The query model is `MultiOracle`'s `IntersectionAlgorithm`, queries $(i,T)$ with $i\in\{0,1\}$ naming the matroid. $\tilde O(n^{7/9})$ is read as $n^{7/9}$ times a fixed power of $\log_2(n+2)$, and "with high probability" as failure probability at most $n^{-c}$ for every $c>0$; the exponent $k$ does not depend on $c$.
--
--   Differences from the source:
--   - encoding: an algorithm making rounds of polynomially many queries → one ExactParallelSampling.QuasiUniform.Protocol (Fin 2 × Finset (Fin n)) Bool (Finset (Fin n)) for every n, with a uniform [0,1]^ℕ tape and measurable next-action maps; reason: the batches and the output depend only on the tape and on earlier answers; a tape of uniform reals simulates any finite random choice, and measurability only restricts the algorithm to be exhibited
--   - encoding: matroids M1, M2 on the same ground set of n elements → two Matroid (Fin n), both with ground set univ, answered by pairOracle M₁ M₂ on queries (0, T) and (1, T); reason: the source's two independence oracles on a common labelled ground set
--   - reading: Õ(n^{7/9}) rounds → ∃ k : ℕ, chosen before c, and C > 0 with at most C(1 + n^{7/9}(log₂(n+2))^k) rounds on every run; reason: Õ hides a polylogarithmic factor; log₂(n+2) ≥ 1 keeps the factor defined and positive at n ≤ 1; the bound holds on every run since runs are truncated; k uniform in c is the stronger reading (amplification is done by parallel repetition)
--   - encoding: polynomially many independence queries (to the two oracles together) per round → at most (n+1)^d independence queries (to the two oracles together) in every batch of every run, d a constant; reason: (n+1)^d covers every polynomial in n, including at n = 0
--   - reading: with high probability → for every c > 0 (with constants and algorithm depending on c), for n ≥ 1 the success probability is at least 1 − n^{−c}; reason: the base mission's reading of the paper's 'with high probability'; the proofs amplify to inverse-polynomial failure for an arbitrary exponent (PDF pp.37, 41); this is the stronger reading
--   - encoding: solves the matroid intersection problem → the output S is independent in M₁ and M₂ and |T| ≤ |S| for every common independent T; reason: the source's definition: S ∈ I1 ∩ I2 of maximum size (PDF p.5)
-- source:
--   Aaron Putterman, Sanjeev Khanna, Junkai Song, STOC 2027 submission #589 (October 2026), A Near-Optimal Parallel Algorithm for Finding Matroid Bases, PDF sha256 71ee2ac010ac681077fc3191139efe918fa4a9b8c6dad648fac2ec33016764d6, Theorem 1.4, p.3 (PDF p.5); proof, p.35 (PDF p.37)

import Mathlib
import Definitions.Def_ParallelMatroidBasis_Main_Supplement_MultiOracle

noncomputable section
open Classical MeasureTheory

namespace ParallelMatroidBasis.Main.Supplement

/-- Theorem 1.4, PDF p.5 (printed p.3), with `Õ(·)` read as a polylogarithmic factor
`(log₂ (n+2))^k` and "with high probability" as failure probability at most `n^{−c}` for every
fixed `c > 0`. There is `k` such that for every `c > 0` there are `C > 0`, `d` and one parallel
algorithm `A` (a protocol for every `n`, seeing `M₁, M₂` only through independence queries to each)
such that for all `n` and all matroids `M₁, M₂` on `Fin n`: every run uses at most
`C (1 + n^{7/9} (log₂ (n+2))^k)` rounds, every round asks at most `(n+1)^d` queries, and for `n ≥ 1`
the output is a maximum-cardinality common independent set with probability at least
`1 − n^{−c}`. -/
theorem theorem_1_4 :
    ∃ k : ℕ, ∀ c : ℝ, 0 < c →
      ∃ (C : ℝ) (d : ℕ) (A : IntersectionAlgorithm), 0 < C ∧
        ∀ (n : ℕ) (M₁ M₂ : Matroid (Fin n)), M₁.E = Set.univ → M₂.E = Set.univ →
          RunRoundsAtMost (A n) (pairOracle M₁ M₂)
            (C * (1 + (n : ℝ) ^ ((7 : ℝ) / 9) * (Real.logb 2 ((n : ℝ) + 2)) ^ k)) ∧
          RunQueriesPerRoundAtMost (A n) (pairOracle M₁ M₂) ((n + 1) ^ d) ∧
          (1 ≤ n → ENNReal.ofReal (1 - (n : ℝ) ^ (-c)) ≤ intersectionSuccessProb A n M₁ M₂)
      := by sorry

end ParallelMatroidBasis.Main.Supplement
