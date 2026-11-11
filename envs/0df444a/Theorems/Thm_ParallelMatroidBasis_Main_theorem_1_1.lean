-- Prove2me | Theorems.Thm_ParallelMatroidBasis_Main_theorem_1_1
-- name    : ParallelMatroidBasis.Main.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:46:50.214199+00:00
-- url     : https://prove2.me/theorems/fb9e123b-bf82-43c7-b5cc-4f1aceb5d012
-- title:
--   Theorem 1.1 — a matroid basis in $O(n^{1/3}\log^{1/3}n)$ rounds of polynomially many independence queries, with high probability
-- statement:
--   For every $c>0$ there are constants $C>0$ and $d\in\mathbb N$ and one parallel algorithm $A$ in the independence-query model (fixed before the matroid, one procedure for every ground-set size $n$, seeing the matroid only through the answers to its queries) such that for every $n$ and every matroid $M$ on the ground set $[n]$:
--   1. every run of $A$ on $M$ uses at most $C\,(1+n^{1/3}(\log_2 n)^{1/3})$ rounds;
--   2. every round asks at most $(n+1)^d$ independence queries;
--   3. if $n\ge1$, $A$ outputs a basis of $M$ with probability at least $1-n^{-c}$:
--   $$\Pr\big[A\text{ outputs a basis of }M\big]\ \ge\ 1-n^{-c}.$$
--
--   This settles the parallel complexity of finding a matroid basis, asked by Karp, Upfal and Wigderson, up to a $\log^{2/3}n$ factor: their lower bound for partition matroids is $\Omega(n^{1/3}/\log^{1/3}n)$ rounds.
--
--   Differences from the source:
--   - encoding: an algorithm making rounds of polynomially many independence queries, outputting a set → one ExactParallelSampling.QuasiUniform.Protocol (Finset (Fin n)) Bool (Finset (Fin n)) for every n, with a uniform [0,1]^ℕ tape and measurable next-action maps, at most (n+1)^d queries in every batch of every run; reason: the batches and the output depend only on the tape and on earlier answers; a tape of uniform reals simulates any finite random choice, and measurability only restricts the algorithm to be exhibited
--   - encoding: a matroid M on n elements → a Matroid (Fin n) with ground set univ; reason: the algorithm knows the n labels of the ground set, as in the source's oracle model
--   - reading: O(n^{1/3} log^{1/3} n) adaptive rounds → ∃ C > 0 with at most C(1 + n^{1/3}(log₂ n)^{1/3}) rounds on every run, for every matroid and every random tape; reason: the paper truncates any run that exceeds C·n^{1/3}log^{1/3}n rounds (PDF p.29), so the bound holds on every run; the additive C covers small n where the main term vanishes; this is the stronger reading
--   - reading: with high probability → for every c > 0 (with C, d, A depending on c) the success probability is at least 1 − n^{−c}; reason: the paper's amplification gives failure N^{−Ω(1)} by O(log N) independent copies and a one-round basis check (PDF p.32), and the authors use the theorem for an arbitrary exponent (Lemma B.2: failure at most n^{−(c+1)}, PDF p.37); every fixed exponent is the stronger reading
--   - encoding: success probability for every n → the probability clause for n ≥ 1; reason: n^{−c} is undefined at n = 0 (Lean's 0^{−c} is 0); the matroid on the empty ground set is excluded only from the probability clause
-- source:
--   Aaron Putterman, Sanjeev Khanna, Junkai Song, STOC 2027 submission #589 (October 2026), A Near-Optimal Parallel Algorithm for Finding Matroid Bases, PDF sha256 71ee2ac010ac681077fc3191139efe918fa4a9b8c6dad648fac2ec33016764d6, Theorem 1.1, p.2 (PDF p.4); proof: Theorem 7.1, p.29 (PDF p.31), and the amplification paragraph, p.30 (PDF p.32); use with an arbitrary exponent: Lemma B.2 and the proof of Theorem 1.4, p.35 (PDF p.37)

import Mathlib
import Definitions.Def_ParallelMatroidBasis_Main_QueryModel

noncomputable section
open Classical MeasureTheory

namespace ParallelMatroidBasis.Main

/-- Theorem 1.1, PDF p.4 (printed p.2), with "with high probability" read as failure probability
at most `n^{−c}` for every fixed `c > 0`. For every `c > 0` there are constants `C > 0`, `d` and
one parallel algorithm `A` (a protocol for every `n`, seeing the matroid only through
independence queries) such that for every `n` and every matroid `M` on `Fin n`: every run uses at
most `C (1 + n^{1/3} (log₂ n)^{1/3})` rounds, every round asks at most `(n+1)^d` independence
queries, and for `n ≥ 1` the output is a basis of `M` with probability at least `1 − n^{−c}`. -/
theorem theorem_1_1 :
    ∀ c : ℝ, 0 < c →
      ∃ (C : ℝ) (d : ℕ) (A : BasisAlgorithm), 0 < C ∧
        ∀ (n : ℕ) (M : Matroid (Fin n)), M.E = Set.univ →
          RoundsAtMost A n M (roundBound C n) ∧
          QueriesPerRoundAtMost A n M ((n + 1) ^ d) ∧
          (1 ≤ n → ENNReal.ofReal (1 - (n : ℝ) ^ (-c)) ≤ successProb A n M) := by sorry

end ParallelMatroidBasis.Main
