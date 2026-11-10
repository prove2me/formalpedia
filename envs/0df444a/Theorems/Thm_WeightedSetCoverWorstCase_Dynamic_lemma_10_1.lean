-- Prove2me | Theorems.Thm_WeightedSetCoverWorstCase_Dynamic_lemma_10_1
-- name    : WeightedSetCoverWorstCase.Dynamic.lemma_10_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:30:31.831934+00:00
-- url     : https://prove2.me/theorems/5cfebf47-faec-4bae-9792-3d0bf59620e4
-- title:
--   Lemma 10.1 — remaining length of a running thread: before $t+100L^2(|(\neg\mathrm{Fr}^B_r)^t|+1/\varepsilon)$; if active, no later than $t+200L^2|(\neg\mathrm{Fr}^B_r)^t|$
-- statement:
--   Let $0<\varepsilon<1/10$ and let $(c,ev)$ be any run on an indefinitely continued legal update stream. If thread $T_r$ is running (active or suspended) at the completed time-unit boundary $t$, put $x=|(\neg\mathrm{Fr}^B_r)^t|$. There exists a later termination event for this same thread identity, at a time-unit index strictly less than $t+100L^2(x+1/\varepsilon)$. If $T_r$ is active at $t$, that termination index is also at most $t+200L^2x$. The input is supplied one update at a time when idle; neither termination nor progress is a premise. Every finite legal history can be continued by alternating legal insertions and deletions when the universe is nonempty; an empty universe has no running thread.
--
--   Differences from the source:
--   - encoding: the algorithm of §7 (Algorithms 1–9), which leaves free the scan order of preprocessing, the order of freezing inside a greedy copy, ties in the greedy selection and ties among cheapest sets → every IsStreamRun of Step ε on an indefinitely continued legal input stream, loading only the next input when idle; c i is the state before event i; reason: the lifetime assertion concerns continued execution of the repeatedly updated dynamic algorithm; the run predicate assumes no progress or termination theorem
--   - reading: an arbitrary initial live set U₀ (§6.1), for which no initialization procedure is given → runs start from the empty state on an update sequence legal from ∅; an initial U₀ is a prefix of insertions; reason: every history (U₀, updates) is the suffix of a legal sequence from ∅ that first inserts U₀; the paper fixes no other initialization
--   - encoding: costs normalized into [1/C, 1] by a common factor, C an integer (§6.1) → levels use ncost s = c(s)/max c, C = ⌈max c / min c⌉, L = max{1, ⌈log_{1+ε}(C n)⌉}, σ = 1000L²/ε, and Algorithm 9's count is ⌈σ⌉; reason: §6.1's normalization made explicit (max c ↦ 1); count > 0 holds exactly ⌈σ⌉ times
--   - encoding: element versions (§6.1), time units and snapshots (§8 notation) → versions are natural numbers in insertion order; crit true counts a time unit, and EndUnit observes its post-state after the following termination check (Algorithm 9, lines 11–13); reason: §12.1 takes completed-unit snapshots before the next activation; the tail case of Claim 12.10 (PDF 62) requires the exhausted thread to have terminated at this boundary
--   - reading: an element inserted while T_k is in preprocessing (footnote 9: scanning it or not does not matter) → it is also queued for scanning, as in the implementation of §13; reason: the paper allows both; §13 scans it, and the time-unit counts follow §13
--   - encoding: on a deletion, the unique running thread owning a coverage that contains e (Algorithm 6, line 6) → the lowest such thread and its first such copy; reason: uniqueness is Lemma 8.8; on reachable states the choice is the paper's
--   - reading: 0 < ε < 1/10 is a sufficiently small constant (§6.1) → every ε with 0 < ε < 1/10; reason: the stronger of the two readings
--   - encoding: T_r terminates before time unit X / no later than time unit Y → there exists a later terminate event M for the same thread identity; its time-unit index is strictly below X and, if initially active, at most Y; reason: this retains actual termination and both printed strictness conventions, including the case where the threshold is an integer
--   - generalization: a finite family S of subsets of the base universe → a finite indexed family of subsets, possibly with repeated underlying subsets; reason: an injective enumeration gives every source instance; positive-cost duplicates do not invalidate the counting, covering, or operational bounds
--   - generalization: the standing polynomial cost-ratio bound of §6.1 → no aspect bound in these structural and lifetime claims; reason: these claims retain L and sigma rather than replacing them by log n; their proofs do not require a polynomial bound on C
-- source:
--   Bhattacharya, Cen, Farokhnejad and Panigrahi (2026), Fully Dynamic Weighted Set Cover: Worst-Case Recourse and Update Time, STOC 2027 submission, supplied PDF sha256 28a86be41fbea2451c118c89c7385500105ced4b59ab5e66110721ebf0909337, Lemma 10.1, p. 39 (PDF 42)

import Mathlib
import Definitions.Def_DynSetCover_Instance
import Definitions.Def_WeightedSetCoverWorstCase_Dynamic_Problem
import Definitions.Def_WeightedSetCoverWorstCase_Dynamic_Algorithm
import Definitions.Def_WeightedSetCoverWorstCase_Dynamic_Analysis

namespace WeightedSetCoverWorstCase.Dynamic

theorem lemma_10_1 (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 10) (inst : Instance)
    (ups : ℕ → Update inst.u) (hups : LegalStream ups)
    (c : ℕ → AlgState inst) (ev : ℕ → Ev) (hrun : IsStreamRun inst ε ups c ev)
    (N : ℕ) (hN : EndUnit c ev N) (T : Thread inst.m) (hT : T ∈ (c (N + 1)).pool) :
    ∃ M : ℕ, N < M ∧ ev M = .terminate ∧
      ((c M).pool.head?.map fun R => R.tid) = some T.tid ∧
      (unitIdx ev M : ℝ) < (unitIdx ev N : ℝ) +
        100 * (Lpar inst ε : ℝ) ^ 2 * ((T.unfrozen.card : ℝ) + 1 / ε) ∧
      ((c (N + 1)).pool.head? = some T →
        (unitIdx ev M : ℝ) ≤ (unitIdx ev N : ℝ) +
          200 * (Lpar inst ε : ℝ) ^ 2 * (T.unfrozen.card : ℝ)) := by sorry

end WeightedSetCoverWorstCase.Dynamic
