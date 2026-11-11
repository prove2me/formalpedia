-- Prove2me | Theorems.Thm_ParallelMatroidBasis_Main_theorem_7_1
-- name    : ParallelMatroidBasis.Main.theorem_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:46:21.862596+00:00
-- url     : https://prove2.me/theorems/fde39e94-7fac-4152-8108-74b733e680e6
-- title:
--   Theorem 7.1 — a basis with probability $\ge 2/3$ in $O(n^{1/3}\log^{1/3}n)$ rounds of polynomially many queries
-- statement:
--   There are constants $C>0$ and $d\in\mathbb N$ and one randomized parallel algorithm $A$ in the independence-query model (fixed before the matroid, one procedure for every ground-set size $n$, seeing the matroid only through answers to its queries) such that for every $n$ and every matroid $M$ on the ground set $[n]$:
--   1. every run of $A$ on $M$ uses at most $C\,(1+n^{1/3}(\log_2 n)^{1/3})$ adaptive rounds;
--   2. every round asks at most $(n+1)^d$ independence queries;
--   3. $A$ outputs a basis of $M$ with probability at least $2/3$:
--   $$\Pr\big[A \text{ outputs a basis of } M\big]\ \ge\ \frac23 .$$
--
--   This is the constant-success version of the main theorem; repeating it $O(\log n)$ times in parallel and keeping a candidate that passes the one-round basis check gives Theorem 1.1.
--
--   Differences from the source:
--   - encoding: an algorithm making rounds of polynomially many independence queries, outputting a set → one ExactParallelSampling.QuasiUniform.Protocol (Finset (Fin n)) Bool (Finset (Fin n)) for every n, with a uniform [0,1]^ℕ tape and measurable next-action maps, at most (n+1)^d queries in every batch of every run; reason: the batches and the output depend only on the tape and on earlier answers; a tape of uniform reals simulates any finite random choice, and measurability only restricts the algorithm to be exhibited
--   - encoding: a matroid M on n elements → a Matroid (Fin n) with ground set univ; reason: the algorithm knows the n labels of the ground set, as in the source's oracle model
--   - reading: O(n^{1/3} log^{1/3} n) adaptive rounds → ∃ C > 0 with at most C(1 + n^{1/3}(log₂ n)^{1/3}) rounds on every run, for every matroid and every random tape; reason: the paper truncates any run that exceeds C·n^{1/3}log^{1/3}n rounds (PDF p.29), so the bound holds on every run; the additive C covers small n where the main term vanishes; this is the stronger reading
-- source:
--   Aaron Putterman, Sanjeev Khanna, Junkai Song, STOC 2027 submission #589 (October 2026), A Near-Optimal Parallel Algorithm for Finding Matroid Bases, PDF sha256 71ee2ac010ac681077fc3191139efe918fa4a9b8c6dad648fac2ec33016764d6, Theorem 7.1, p.29 (PDF p.31), proof pp.29–30 (PDF pp.31–32); truncation, p.27 (PDF p.29)

import Mathlib
import Definitions.Def_ParallelMatroidBasis_Main_QueryModel

noncomputable section
open Classical MeasureTheory

namespace ParallelMatroidBasis.Main

/-- Theorem 7.1, PDF p.31 (printed p.29). There are constants `C > 0`, `d` and one randomized
parallel algorithm `A` (a protocol for every `n`, seeing the matroid only through independence
queries) such that for every `n` and every matroid `M` on `Fin n`: every run uses at most
`C (1 + n^{1/3} (log₂ n)^{1/3})` adaptive rounds, every round asks at most `(n+1)^d` independence
queries, and `A` outputs a basis of `M` with probability at least `2/3`. -/
theorem theorem_7_1 :
    ∃ (C : ℝ) (d : ℕ) (A : BasisAlgorithm), 0 < C ∧
      ∀ (n : ℕ) (M : Matroid (Fin n)), M.E = Set.univ →
        RoundsAtMost A n M (roundBound C n) ∧
        QueriesPerRoundAtMost A n M ((n + 1) ^ d) ∧
        ENNReal.ofReal (2 / 3) ≤ successProb A n M := by sorry

end ParallelMatroidBasis.Main
