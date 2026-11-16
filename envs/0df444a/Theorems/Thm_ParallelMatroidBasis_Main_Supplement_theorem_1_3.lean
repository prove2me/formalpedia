-- Prove2me | Theorems.Thm_ParallelMatroidBasis_Main_Supplement_theorem_1_3
-- name    : ParallelMatroidBasis.Main.Supplement.theorem_1_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:02:21.087948+00:00
-- url     : https://prove2.me/theorems/d3044994-ed45-4674-ad57-9d7263d4ef1a
-- title:
--   Theorem 1.3 — a deterministic algorithm finds a basis of every linear matroid in $O(n^{1/3}\log^{1/3}n)$ rounds
-- statement:
--   There are constants $C>0$ and $d\in\mathbb N$ and one (non-uniform) **deterministic** parallel algorithm $A$ in the independence-query model — one procedure for every ground-set size $n$, whose queries and output depend only on the answers to its earlier queries, never on random bits — such that for every $n$ and every linear matroid $M$ on the ground set $[n]$:
--
--   1. the run of $A$ on $M$ uses at most $C\,(1+n^{1/3}(\log_2 n)^{1/3})$ adaptive rounds;
--   2. every round asks at most $(n+1)^d$ independence queries;
--   3. the run halts and outputs a basis of $M$.
--
--   In short, a basis of a linear matroid can be found deterministically within
--   $$O\big(n^{1/3}\log^{1/3} n\big)$$
--   rounds of polynomially many independence queries. Since the Karp–Upfal–Wigderson lower bound $\Omega(n^{1/3}/\log^{1/3}n)$ holds for linear matroids even against randomized algorithms, this matches it up to a $\log^{2/3}n$ factor without randomness.
--
--   **Formalization Note** The algorithm is a family of protocols indexed by $n$ with no uniformity requirement, which is what "non-uniform" allows. Determinism is stated as: the next action is the same for every random tape. Correctness is required on every run.
--
--   Differences from the source:
--   - encoding: an algorithm making rounds of polynomially many queries → one ExactParallelSampling.QuasiUniform.Protocol (Finset (Fin n)) Bool (Finset (Fin n)) for every n, with a uniform [0,1]^ℕ tape and measurable next-action maps; reason: the batches and the output depend only on the tape and on earlier answers; a tape of uniform reals simulates any finite random choice, and measurability only restricts the algorithm to be exhibited
--   - encoding: a matroid M on n elements → a Matroid (Fin n) with ground set univ; reason: the algorithm knows the n labels of the ground set, as in the source's oracle model (same convention as the base mission)
--   - generalization: linear matroid: representable by vectors over a field F_q → representable (RandDelMatroid.Indep.IsRepresentableOver) over some field F : Type, finite or not, vectors in F^k for some k, repeated vectors allowed; reason: every F_q-representable matroid is included, so the Lean statement specializes to the source's; the cited bound [Nel16] counts matroids representable over any field, and the proof of Theorem 1.3 uses only that count
--   - encoding: a (non-uniform) deterministic algorithm → a BasisAlgorithm, an arbitrary family of protocols indexed by n, whose next-action map does not depend on the tape; the output is a basis on every tape; reason: a protocol constant in the tape is exactly a deterministic adaptive query algorithm; non-uniformity means the family need not be generated uniformly in n, which an arbitrary Lean family allows
--   - reading: O(n^{1/3} log^{1/3} n) rounds → ∃ C > 0 with at most C(1 + n^{1/3}(log₂ n)^{1/3}) rounds on the run, for every linear matroid; reason: logarithms are base 2 (PDF p.12); the additive C covers small n where the main term vanishes; for a deterministic algorithm there is one run
--   - encoding: polynomially many independence queries per round → at most (n+1)^d independence queries in every batch of every run, d a constant; reason: (n+1)^d covers every polynomial in n, including at n = 0
-- source:
--   Aaron Putterman, Sanjeev Khanna, Junkai Song, STOC 2027 submission #589 (October 2026), A Near-Optimal Parallel Algorithm for Finding Matroid Bases, PDF sha256 71ee2ac010ac681077fc3191139efe918fa4a9b8c6dad648fac2ec33016764d6, Theorem 1.3, p.2 (PDF p.4); proof, p.39 (PDF p.41), using Theorem 7.1 and Claim D.1; linear matroids: §1, p.2 (PDF p.4)

import Mathlib
import Definitions.Def_ParallelMatroidBasis_Main_QueryModel
import Definitions.Def_ParallelMatroidBasis_Main_Supplement_Classes

noncomputable section
open Classical MeasureTheory

namespace ParallelMatroidBasis.Main.Supplement

open ExactParallelSampling.QuasiUniform

/-- Theorem 1.3, PDF p.4 (printed p.2). There are constants `C > 0`, `d` and one deterministic
parallel algorithm `A` (a protocol for every `n` — chosen non-uniformly — whose next action never
depends on the random tape, seeing the matroid only through independence queries) such that for
every `n` and every linear matroid `M` on `Fin n`: every run uses at most
`C (1 + n^{1/3} (log₂ n)^{1/3})` rounds, every round asks at most `(n+1)^d` independence queries,
and the run halts with a basis of `M`. -/
theorem theorem_1_3 :
    ∃ (C : ℝ) (d : ℕ) (A : ParallelMatroidBasis.Main.BasisAlgorithm), 0 < C ∧
      (∀ (n : ℕ) (h : Transcript (Finset (Fin n)) Bool) (ω ω' : Tape),
        (A n).next h ω = (A n).next h ω') ∧
      ∀ (n : ℕ) (M : Matroid (Fin n)), M.E = Set.univ → IsLinearMatroid M →
        ParallelMatroidBasis.Main.RoundsAtMost A n M (ParallelMatroidBasis.Main.roundBound C n) ∧
        ParallelMatroidBasis.Main.QueriesPerRoundAtMost A n M ((n + 1) ^ d) ∧
        ∀ ω : Tape, ∃ B : Finset (Fin n),
          (A n).output (ParallelMatroidBasis.Main.indOracle M) ω = some B ∧
            M.IsBase (↑B : Set (Fin n)) := by sorry

end ParallelMatroidBasis.Main.Supplement
