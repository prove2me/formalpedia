-- Prove2me | Theorems.Thm_WeightedSetCoverWorstCase_Dynamic_lemma_7_3
-- name    : WeightedSetCoverWorstCase.Dynamic.lemma_7_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:30:18.632507+00:00
-- url     : https://prove2.me/theorems/1fa2131a-5787-4be3-be27-6b3d2ca4c6ea
-- title:
--   Lemma 7.3 — the output $C^F+C^B$ covers every alive element at the end of every time unit
-- statement:
--   Let $0<\varepsilon<1/10$ and let $(c,ev)$ be any run of the algorithm on an update sequence legal from the empty live set. If event $N$ ends a time unit, then in the state just after it every alive version $v$ belongs to (the input set of) some copy of the output $C^F+C^B$.
--
--   Differences from the source:
--   - encoding: the algorithm of §7 (Algorithms 1–9), which leaves free the scan order of preprocessing, the order of freezing inside a greedy copy, ties in the greedy selection and ties among cheapest sets → every run (c, ev) of the transition relation Step ε (IsRun), every free choice ranging over all allowed values; c i is the state before event i; reason: the paper's claims are made for every resolution of these choices; quantifying over all runs states them for all
--   - reading: an arbitrary initial live set U₀ (§6.1), for which no initialization procedure is given → runs start from the empty state on an update sequence legal from ∅; an initial U₀ is a prefix of insertions; reason: every history (U₀, updates) is the suffix of a legal sequence from ∅ that first inserts U₀; the paper fixes no other initialization
--   - encoding: costs normalized into [1/C, 1] by a common factor, C an integer (§6.1) → levels use ncost s = c(s)/max c, C = ⌈max c / min c⌉, L = max{1, ⌈log_{1+ε}(C n)⌉}, σ = 1000L²/ε, and Algorithm 9's count is ⌈σ⌉; reason: §6.1's normalization made explicit (max c ↦ 1); count > 0 holds exactly ⌈σ⌉ times
--   - encoding: element versions (§6.1), time units and snapshots (§8 notation) → versions are natural numbers in insertion order; crit true counts a time unit, and EndUnit observes its post-state after the following termination check (Algorithm 9, lines 11–13); reason: §12.1 takes completed-unit snapshots before the next activation; the tail case of Claim 12.10 (PDF 62) requires the exhausted thread to have terminated at this boundary
--   - reading: an element inserted while T_k is in preprocessing (footnote 9: scanning it or not does not matter) → it is also queued for scanning, as in the implementation of §13; reason: the paper allows both; §13 scans it, and the time-unit counts follow §13
--   - encoding: on a deletion, the unique running thread owning a coverage that contains e (Algorithm 6, line 6) → the lowest such thread and its first such copy; reason: uniqueness is Lemma 8.8; on reachable states the choice is the paper's
--   - reading: 0 < ε < 1/10 is a sufficiently small constant (§6.1) → every ε with 0 < ε < 1/10; reason: the stronger of the two readings
--   - generalization: a finite family S of subsets of the base universe → a finite indexed family of subsets, possibly with repeated underlying subsets; reason: an injective enumeration gives every source instance; positive-cost duplicates do not invalidate the counting, covering, or operational bounds
--   - generalization: the standing polynomial cost-ratio bound of §6.1 → no aspect bound in these structural and lifetime claims; reason: these claims retain L and sigma rather than replacing them by log n; their proofs do not require a polynomial bound on C
-- source:
--   Bhattacharya, Cen, Farokhnejad and Panigrahi (2026), Fully Dynamic Weighted Set Cover: Worst-Case Recourse and Update Time, STOC 2027 submission, supplied PDF sha256 28a86be41fbea2451c118c89c7385500105ced4b59ab5e66110721ebf0909337, Lemma 7.3, p. 32 (PDF 35)

import Mathlib
import Definitions.Def_DynSetCover_Instance
import Definitions.Def_WeightedSetCoverWorstCase_Dynamic_Problem
import Definitions.Def_WeightedSetCoverWorstCase_Dynamic_Algorithm

import Definitions.Def_WeightedSetCoverWorstCase_Dynamic_Analysis

namespace WeightedSetCoverWorstCase.Dynamic

theorem lemma_7_3 (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 10) (inst : Instance)
    (ups : List (Update inst.u)) (hups : LegalSeq ∅ ups) (c : ℕ → AlgState inst) (ev : ℕ → Ev)
    (hrun : IsRun inst ε ups c ev)
    (N : ℕ) (hN : EndUnit c ev N) :
    ∀ v ∈ (c (N + 1)).alive, ∃ cp ∈ (c (N + 1)).outCopies, (c (N + 1)).InSet cp.set v := by sorry

end WeightedSetCoverWorstCase.Dynamic
