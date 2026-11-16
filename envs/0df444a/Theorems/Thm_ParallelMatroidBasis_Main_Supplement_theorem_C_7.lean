-- Prove2me | Theorems.Thm_ParallelMatroidBasis_Main_Supplement_theorem_C_7
-- name    : ParallelMatroidBasis.Main.Supplement.theorem_C_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:05:02.951417+00:00
-- url     : https://prove2.me/theorems/2d9e02e9-f48c-4b43-b936-3f58b2da2333
-- title:
--   Theorem C.7 — a basis of a partition matroid in $O(n^{1/3}/\log^{1/3}n)$ rounds, with high probability
-- statement:
--   For every $c>0$ there are constants $C>0$, $d\in\mathbb N$ and one randomized parallel algorithm $A$ in the independence-query model — one procedure for every ground-set size $n$, seeing the matroid only through independence queries — such that for every $n$ and every partition matroid $M$ on the ground set $[n]$ (Definition C.1):
--
--   1. every run uses at most
--   $$C\Big(1+\frac{n^{1/3}}{(\log_2 n)^{1/3}}\Big)$$
--   adaptive rounds;
--   2. every round asks at most $(n+1)^d$ independence queries;
--   3. if $n\ge1$, the output is a basis of $M$ with probability at least $1-n^{-c}$.
--
--   On partition matroids this is a strictly smaller round bound than the $O(n^{1/3}\log^{1/3}n)$ of Theorem 1.1, and it matches the Karp–Upfal–Wigderson lower bound $\Omega(n^{1/3}/\log^{1/3}n)$ for this class; so a sharper analysis of that lower-bound instance cannot close the remaining $\log^{2/3}n$ gap.
--
--   **Formalization Note** The model is the base mission's `QueryModel` (`BasisAlgorithm`, `RoundsAtMost`, `QueriesPerRoundAtMost`, `successProb`). For $n\le1$ Lean evaluates $\log_2 n=0$ and $x/0=0$, so the round bound reads $C$, which is the intended constant budget for trivial ground sets.
--
--   Differences from the source:
--   - encoding: an algorithm making rounds of polynomially many queries → one ExactParallelSampling.QuasiUniform.Protocol (Finset (Fin n)) Bool (Finset (Fin n)) for every n, with a uniform [0,1]^ℕ tape and measurable next-action maps; reason: the batches and the output depend only on the tape and on earlier answers; a tape of uniform reals simulates any finite random choice, and measurability only restricts the algorithm to be exhibited
--   - encoding: any partition matroid M on n elements → a Matroid (Fin n) satisfying IsPartitionMatroid (ground set univ, parts pairwise disjoint and covering, empty parts allowed); reason: empty parts have budget 0 and impose no constraint, so the class is that of Definition C.1
--   - reading: O(n^{1/3}/log^{1/3}(n)) adaptive rounds → ∃ C > 0 with at most C(1 + n^{1/3}/(log₂ n)^{1/3}) rounds on every run; reason: logarithms are base 2; the proof truncates each trial after C(1 + n^{1/3}/log^{1/3}(n+1)) rounds (PDF p.41), so the bound holds on every run; for n ≤ 1, Lean's log₂ n = 0 and x/0 = 0 make the bound C
--   - encoding: polynomially many independence queries per round → at most (n+1)^d independence queries in every batch of every run, d a constant; reason: (n+1)^d covers every polynomial in n, including at n = 0
--   - reading: with high probability → for every c > 0 (with constants and algorithm depending on c), for n ≥ 1 the success probability is at least 1 − n^{−c}; reason: the base mission's reading of the paper's 'with high probability'; the proofs amplify to inverse-polynomial failure for an arbitrary exponent (PDF pp.37, 41); this is the stronger reading
-- source:
--   Aaron Putterman, Sanjeev Khanna, Junkai Song, STOC 2027 submission #589 (October 2026), A Near-Optimal Parallel Algorithm for Finding Matroid Bases, PDF sha256 71ee2ac010ac681077fc3191139efe918fa4a9b8c6dad648fac2ec33016764d6, Theorem C.7, p.38 (PDF p.40); proof, pp.38–39 (PDF pp.40–41); Definition C.1, p.36 (PDF p.38)

import Mathlib
import Definitions.Def_ParallelMatroidBasis_Main_QueryModel
import Definitions.Def_ParallelMatroidBasis_Main_Supplement_Classes

noncomputable section
open Classical MeasureTheory

namespace ParallelMatroidBasis.Main.Supplement

/-- Theorem C.7, PDF p.40 (printed p.38), with "with high probability" read as failure
probability at most `n^{−c}` for every fixed `c > 0`. For every `c > 0` there are `C > 0`, `d` and
one randomized parallel algorithm `A` (a protocol for every `n`, seeing the matroid only through
independence queries) such that for every `n` and every partition matroid `M` on `Fin n`: every run
uses at most `C (1 + n^{1/3} / (log₂ n)^{1/3})` adaptive rounds, every round asks at most `(n+1)^d`
independence queries, and for `n ≥ 1` the output is a basis of `M` with probability at least
`1 − n^{−c}`. (For `n ≤ 1`, `log₂ n = 0` and the bound reads `C`.) -/
theorem theorem_C_7 :
    ∀ c : ℝ, 0 < c →
      ∃ (C : ℝ) (d : ℕ) (A : ParallelMatroidBasis.Main.BasisAlgorithm), 0 < C ∧
        ∀ (n : ℕ) (M : Matroid (Fin n)), IsPartitionMatroid M →
          ParallelMatroidBasis.Main.RoundsAtMost A n M
            (C * (1 + (n : ℝ) ^ ((1 : ℝ) / 3) / (Real.logb 2 n) ^ ((1 : ℝ) / 3))) ∧
          ParallelMatroidBasis.Main.QueriesPerRoundAtMost A n M ((n + 1) ^ d) ∧
          (1 ≤ n →
            ENNReal.ofReal (1 - (n : ℝ) ^ (-c)) ≤ ParallelMatroidBasis.Main.successProb A n M)
      := by sorry

end ParallelMatroidBasis.Main.Supplement
