-- Prove2me | Theorems.Thm_WeightedSetCoverWorstCase_Dynamic_lemma_9_1
-- name    : WeightedSetCoverWorstCase.Dynamic.lemma_9_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:30:48.361171+00:00
-- url     : https://prove2.me/theorems/b93249d7-117c-4fab-9670-9841e5d6f083
-- title:
--   Lemma 9.1 — worst-case recourse $O(\sigma/\varepsilon)=O(\log^2 n/\varepsilon^4)$ per adversarial update
-- statement:
--   There is an absolute constant $K$ such that for every $0<\varepsilon<1/10$, every instance, every legal update sequence and every run, the recourse of the output multiset $C^F+C^B$ between the idle state before an adversarial update and the idle state after it is at most $K\sigma/\varepsilon$. Moreover, for every aspect exponent $d$ there is $K'_d$ such that, on instances with $c(s)\le\max(2,n)^d c(s')$, it is at most $K'_d(1+\log\max(1,n))^2/\varepsilon^4$, for every $0<\varepsilon<1/10$.
--   Recourse counts copies: $|A\setminus B|+|B\setminus A|$ for the multisets of copies (input set, coverage, level); a copy moved from a buffer to the foreground is unchanged.
--
--   Differences from the source:
--   - encoding: the algorithm of §7 (Algorithms 1–9), which leaves free the scan order of preprocessing, the order of freezing inside a greedy copy, ties in the greedy selection and ties among cheapest sets → every run (c, ev) of the transition relation Step ε (IsRun), every free choice ranging over all allowed values; c i is the state before event i; reason: the paper's claims are made for every resolution of these choices; quantifying over all runs states them for all
--   - reading: an arbitrary initial live set U₀ (§6.1), for which no initialization procedure is given → runs start from the empty state on an update sequence legal from ∅; an initial U₀ is a prefix of insertions; reason: every history (U₀, updates) is the suffix of a legal sequence from ∅ that first inserts U₀; the paper fixes no other initialization
--   - encoding: costs normalized into [1/C, 1] by a common factor, C an integer (§6.1) → levels use ncost s = c(s)/max c, C = ⌈max c / min c⌉, L = max{1, ⌈log_{1+ε}(C n)⌉}, σ = 1000L²/ε, and Algorithm 9's count is ⌈σ⌉; reason: §6.1's normalization made explicit (max c ↦ 1); count > 0 holds exactly ⌈σ⌉ times
--   - encoding: element versions (§6.1), time units and snapshots (§8 notation) → versions are natural numbers in insertion order; crit true counts a time unit, and EndUnit observes its post-state after the following termination check (Algorithm 9, lines 11–13); reason: §12.1 takes completed-unit snapshots before the next activation; the tail case of Claim 12.10 (PDF 62) requires the exhausted thread to have terminated at this boundary
--   - reading: an element inserted while T_k is in preprocessing (footnote 9: scanning it or not does not matter) → it is also queued for scanning, as in the implementation of §13; reason: the paper allows both; §13 scans it, and the time-unit counts follow §13
--   - encoding: on a deletion, the unique running thread owning a coverage that contains e (Algorithm 6, line 6) → the lowest such thread and its first such copy; reason: uniqueness is Lemma 8.8; on reachable states the choice is the paper's
--   - reading: 0 < ε < 1/10 is a sufficiently small constant (§6.1) → every ε with 0 < ε < 1/10; reason: the stronger of the two readings
--   - encoding: at any time step → between two idle states of the run whose remaining inputs differ by exactly one update; reason: a time step is the processing of one adversarial update, which starts and ends with the scheduler idle
--   - reading: the recourse of the multiset output C^F + C^B → copy-level multiset symmetric difference (copyRecourse); reason: §6.1: solutions are multisets; §9 counts insertions and removals of sets in C^F + C^B; it bounds the deduplicated recourse
--   - encoding: O(σ/ε) = O(log² n/ε⁴) → K σ/ε with K absolute; and, under C ≤ poly(n) with exponent d, K'_d (1 + log max(1,n))²/ε⁴ with K'_d independent of ε; reason: the source's ε-dependence is explicit; the second form uses the standing aspect assumption, as the source does
--   - generalization: a finite family S of subsets of the base universe → a finite indexed family of subsets, possibly with repeated underlying subsets; reason: an injective enumeration gives every source instance; positive-cost duplicates do not invalidate the counting, covering, or operational bounds
-- source:
--   Bhattacharya, Cen, Farokhnejad and Panigrahi (2026), Fully Dynamic Weighted Set Cover: Worst-Case Recourse and Update Time, STOC 2027 submission, supplied PDF sha256 28a86be41fbea2451c118c89c7385500105ced4b59ab5e66110721ebf0909337, Lemma 9.1, p. 38 (PDF 41)

import Mathlib
import Definitions.Def_DynSetCover_Instance
import Definitions.Def_WeightedSetCoverWorstCase_Dynamic_Problem
import Definitions.Def_WeightedSetCoverWorstCase_Dynamic_Algorithm

namespace WeightedSetCoverWorstCase.Dynamic

theorem lemma_9_1 :
    ∃ K : ℝ,
      (∀ (ε : ℝ), 0 < ε → ε < 1 / 10 → ∀ (inst : Instance) (ups : List (Update inst.u)),
        LegalSeq ∅ ups → ∀ (c : ℕ → AlgState inst) (ev : ℕ → Ev), IsRun inst ε ups c ev →
        ∀ N₁ N₂ : ℕ, (c N₁).mode = Mode.idle → (c N₂).mode = Mode.idle →
          (c N₁).rest.length = (c N₂).rest.length + 1 →
          (copyRecourse (c N₁).outCopies (c N₂).outCopies : ℝ) ≤ K * sigma inst ε / ε) ∧
      ∀ d : ℕ, ∃ K' : ℝ,
        ∀ (ε : ℝ), 0 < ε → ε < 1 / 10 → ∀ (inst : Instance), AspectBound inst d →
        ∀ (ups : List (Update inst.u)), LegalSeq ∅ ups →
        ∀ (c : ℕ → AlgState inst) (ev : ℕ → Ev), IsRun inst ε ups c ev →
        ∀ N₁ N₂ : ℕ, (c N₁).mode = Mode.idle → (c N₂).mode = Mode.idle →
          (c N₁).rest.length = (c N₂).rest.length + 1 →
          (copyRecourse (c N₁).outCopies (c N₂).outCopies : ℝ) ≤
            K' * (1 + Real.log (max 1 (inst.u : ℝ))) ^ 2 / ε ^ 4 := by sorry

end WeightedSetCoverWorstCase.Dynamic
