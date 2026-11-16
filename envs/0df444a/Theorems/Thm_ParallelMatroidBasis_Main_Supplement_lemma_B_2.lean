-- Prove2me | Theorems.Thm_ParallelMatroidBasis_Main_Supplement_lemma_B_2
-- name    : ParallelMatroidBasis.Main.Supplement.lemma_B_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:03:24.822031+00:00
-- url     : https://prove2.me/theorems/203ff499-50dd-437e-b353-bf1320b058ad
-- title:
--   Lemma B.2 — random feasible sequences in $\tilde O(n^{1/3})$ rounds, up to a coupling failure of $n^{-c}$
-- statement:
--   There is an exponent $k\in\mathbb N$ such that for every fixed $c>0$ there are constants $C>0$, $d\in\mathbb N$ and one randomized parallel algorithm $A$ — one procedure for every ground-set size $n$, seeing a matroid only through independence queries, outputting a finite sequence of elements — such that for every $n\ge2$ and every matroid $M=(E,\mathcal I)$ on $E=[n]$:
--
--   1. every run uses at most $C\,(1+n^{1/3}(\log_2 n)^k)$ adaptive rounds;
--   2. every round asks at most $(n+1)^d$ independence queries;
--   3. the output of $A$ can be coupled to a random feasible sequence of $M$ (Definition B.1, law $\mu_M$) so that the two agree with probability at least $1-n^{-c}$; equivalently,
--   $$\sum_{s}\min\big(\Pr[A \text{ outputs } s],\ \mu_M(s)\big)\ \ge\ 1-n^{-c},$$
--   the sum running over all finite sequences $s$ of elements.
--
--   The left side of the display is the largest probability of agreement over all couplings of the output law with $\mu_M$. The lemma applies to every matroid, in particular to every restriction and contraction, which is what the reduction of [BRS19b] (Lemma B.3) needs to obtain Theorem 1.5.
--
--   **Formalization Note** The output type is `List (Fin n)`; a run that never halts outputs nothing and contributes no mass. $\tilde O(n^{1/3})$ is read as $n^{1/3}$ times a fixed power of $\log_2 n$ (which is $\ge1$ for $n\ge2$), with the exponent $k$ chosen before $c$.
--
--   Differences from the source:
--   - encoding: an algorithm making rounds of polynomially many queries → one ExactParallelSampling.QuasiUniform.Protocol (Finset (Fin n)) Bool (List (Fin n)) for every n, with a uniform [0,1]^ℕ tape and measurable next-action maps; reason: the batches and the output depend only on the tape and on earlier answers; a tape of uniform reals simulates any finite random choice, and measurability only restricts the algorithm to be exhibited
--   - encoding: a matroid M on n elements → a Matroid (Fin n) with ground set univ; reason: the algorithm knows the n labels of the ground set, as in the source's oracle model (same convention as the base mission)
--   - reading: for every fixed c > 0, an Õ(n^{1/3}) round algorithm → ∃ k : ℕ chosen before c; for each c, ∃ C > 0 with at most C(1 + n^{1/3}(log₂ n)^k) rounds on every run; reason: Õ hides a polylogarithmic factor (log₂ n ≥ 1 for n ≥ 2); the bound holds on every run since runs are truncated; k uniform in c is the stronger reading
--   - encoding: polynomially many independence queries per round → at most (n+1)^d independence queries in every batch of every run, d a constant; reason: (n+1)^d covers every polynomial in n, including at n = 0
--   - encoding: the output can be coupled to a random feasible sequence so that the two agree with probability at least 1 − n^{−c} → ∑' s, min(Pr[output = some s], μ_M(s)) ≥ 1 − n^{−c} over s : List (Fin n); reason: for two discrete laws the largest agreement probability of a coupling equals the sum of the pointwise minima, so the two conditions are equivalent
--   - encoding: a random feasible sequence (a_1, …, a_{rank(M)}) → the law feasibleSeqLaw M on List (Fin n): product of uniform step probabilities, stopping when no feasible element remains; reason: the feasible set is nonempty exactly while fewer than rank(M) elements have been chosen, so the stopping rule gives length rank(M)
-- source:
--   Aaron Putterman, Sanjeev Khanna, Junkai Song, STOC 2027 submission #589 (October 2026), A Near-Optimal Parallel Algorithm for Finding Matroid Bases, PDF sha256 71ee2ac010ac681077fc3191139efe918fa4a9b8c6dad648fac2ec33016764d6, Lemma B.2, p.35 (PDF p.37); Definition B.1 ([BRS19b]), p.35 (PDF p.37)

import Mathlib
import Definitions.Def_ExactParallelSampling_QuasiUniform_Protocol
import Definitions.Def_ParallelMatroidBasis_Main_QueryModel
import Definitions.Def_ParallelMatroidBasis_Main_Supplement_MultiOracle
import Definitions.Def_ParallelMatroidBasis_Main_Supplement_FeasibleSequence

noncomputable section
open Classical MeasureTheory

namespace ParallelMatroidBasis.Main.Supplement

open ExactParallelSampling.QuasiUniform

/-- Lemma B.2, PDF p.37 (printed p.35), with `Õ(·)` read as a polylogarithmic factor
`(log₂ n)^k`. There is `k` such that for every `c > 0` there are `C > 0`, `d` and one parallel
algorithm `A` (a protocol for every `n`, seeing the matroid only through independence queries,
outputting a list of elements) such that for every `n ≥ 2` and every matroid `M` on `Fin n`: every
run uses at most `C (1 + n^{1/3} (log₂ n)^k)` rounds, every round asks at most `(n+1)^d`
independence queries, and the output can be coupled with a random feasible sequence of `M` so that
the two agree with probability at least `1 − n^{−c}`; that is,
`∑_s min(Pr[A outputs s], μ_M(s)) ≥ 1 − n^{−c}`, where `μ_M` is the law of a random feasible
sequence (the left side is the largest agreement probability over all couplings). -/
theorem lemma_B_2 :
    ∃ k : ℕ, ∀ c : ℝ, 0 < c →
      ∃ (C : ℝ) (d : ℕ) (A : (n : ℕ) → Protocol (Finset (Fin n)) Bool (List (Fin n))), 0 < C ∧
        ∀ (n : ℕ), 2 ≤ n → ∀ M : Matroid (Fin n), M.E = Set.univ →
          RunRoundsAtMost (A n) (ParallelMatroidBasis.Main.indOracle M)
            (C * (1 + (n : ℝ) ^ ((1 : ℝ) / 3) * (Real.logb 2 n) ^ k)) ∧
          RunQueriesPerRoundAtMost (A n) (ParallelMatroidBasis.Main.indOracle M) ((n + 1) ^ d) ∧
          ENNReal.ofReal (1 - (n : ℝ) ^ (-c)) ≤
            ∑' s : List (Fin n),
              min (tapeLaw {ω | (A n).output (ParallelMatroidBasis.Main.indOracle M) ω = some s})
                (ENNReal.ofReal (feasibleSeqLaw M s)) := by sorry

end ParallelMatroidBasis.Main.Supplement
