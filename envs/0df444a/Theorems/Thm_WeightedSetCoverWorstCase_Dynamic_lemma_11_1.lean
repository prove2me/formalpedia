-- Prove2me | Theorems.Thm_WeightedSetCoverWorstCase_Dynamic_lemma_11_1
-- name    : WeightedSetCoverWorstCase.Dynamic.lemma_11_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:30:26.679591+00:00
-- url     : https://prove2.me/theorems/b5de1a8d-0a7e-4036-92c6-a6203d8dbd1a
-- title:
--   Lemma 11.1 — the foreground cost is $O(\log n)\cdot\mathrm{OPT}$ at the end of every time unit and after every update
-- statement:
--   For every $0<\varepsilon<1/10$ there is $K$ such that for every instance, every legal update sequence and every run: at the end of every time unit, and in every idle state (the end of processing an adversarial update), the total cost of the copies of $C^F$ (original costs, every copy paid) is at most $K(1+\log\max(1,n))\cdot\mathrm{OPT}$, where $\mathrm{OPT}$ is the minimum cost of a set cover of the alive elements at that moment.
--
--   Differences from the source:
--   - encoding: the algorithm of §7 (Algorithms 1–9), which leaves free the scan order of preprocessing, the order of freezing inside a greedy copy, ties in the greedy selection and ties among cheapest sets → every run (c, ev) of the transition relation Step ε (IsRun), every free choice ranging over all allowed values; c i is the state before event i; reason: the paper's claims are made for every resolution of these choices; quantifying over all runs states them for all
--   - reading: an arbitrary initial live set U₀ (§6.1), for which no initialization procedure is given → runs start from the empty state on an update sequence legal from ∅; an initial U₀ is a prefix of insertions; reason: every history (U₀, updates) is the suffix of a legal sequence from ∅ that first inserts U₀; the paper fixes no other initialization
--   - encoding: costs normalized into [1/C, 1] by a common factor, C an integer (§6.1) → levels use ncost s = c(s)/max c, C = ⌈max c / min c⌉, L = max{1, ⌈log_{1+ε}(C n)⌉}, σ = 1000L²/ε, and Algorithm 9's count is ⌈σ⌉; reason: §6.1's normalization made explicit (max c ↦ 1); count > 0 holds exactly ⌈σ⌉ times
--   - encoding: element versions (§6.1), time units and snapshots (§8 notation) → versions are natural numbers in insertion order; crit true counts a time unit, and EndUnit observes its post-state after the following termination check (Algorithm 9, lines 11–13); reason: §12.1 takes completed-unit snapshots before the next activation; the tail case of Claim 12.10 (PDF 62) requires the exhausted thread to have terminated at this boundary
--   - reading: an element inserted while T_k is in preprocessing (footnote 9: scanning it or not does not matter) → it is also queued for scanning, as in the implementation of §13; reason: the paper allows both; §13 scans it, and the time-unit counts follow §13
--   - encoding: on a deletion, the unique running thread owning a coverage that contains e (Algorithm 6, line 6) → the lowest such thread and its first such copy; reason: uniqueness is Lemma 8.8; on reachable states the choice is the paper's
--   - reading: 0 < ε < 1/10 is a sufficiently small constant (§6.1) → every ε with 0 < ε < 1/10; reason: the stronger of the two readings
--   - encoding: an O(log n) approximation (ε a fixed constant) → ∃ K depending only on ε, chosen before the instance and the run, with cost ≤ K (1 + log max(1,n)) · OPT; reason: the additive 1 makes the bound meaningful at n = 1
--   - generalization: the standing assumption C ≤ poly(n) (footnote 1) → no aspect-ratio hypothesis; reason: footnote 1: the approximation bound does not depend on C; the Lean statement implies the source's
--   - encoding: at the end of processing every adversarial update → in every idle state of the run; reason: the scheduler is idle exactly between the processing of two updates
--   - generalization: a finite family S of subsets of the base universe → a finite indexed family of subsets, possibly with repeated underlying subsets; reason: an injective enumeration gives every source instance; positive-cost duplicates do not invalidate the counting, covering, or operational bounds
-- source:
--   Bhattacharya, Cen, Farokhnejad and Panigrahi (2026), Fully Dynamic Weighted Set Cover: Worst-Case Recourse and Update Time, STOC 2027 submission, supplied PDF sha256 28a86be41fbea2451c118c89c7385500105ced4b59ab5e66110721ebf0909337, Lemma 11.1, p. 45 (PDF 48)

import Mathlib
import Definitions.Def_DynSetCover_Instance
import Definitions.Def_WeightedSetCoverWorstCase_Dynamic_Problem
import Definitions.Def_WeightedSetCoverWorstCase_Dynamic_Algorithm

import Definitions.Def_WeightedSetCoverWorstCase_Dynamic_Analysis

namespace WeightedSetCoverWorstCase.Dynamic

theorem lemma_11_1 (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 10) :
    ∃ K : ℝ, ∀ (inst : Instance) (ups : List (Update inst.u)), LegalSeq ∅ ups →
      ∀ (c : ℕ → AlgState inst) (ev : ℕ → Ev), IsRun inst ε ups c ev →
      (∀ N : ℕ, EndUnit c ev N →
        copiesCost inst (c (N + 1)).fg.C ≤
          K * (1 + Real.log (max 1 (inst.u : ℝ))) * (c (N + 1)).optAlive) ∧
      (∀ N : ℕ, (c N).mode = Mode.idle →
        copiesCost inst (c N).fg.C ≤ K * (1 + Real.log (max 1 (inst.u : ℝ))) * (c N).optAlive) := by sorry

end WeightedSetCoverWorstCase.Dynamic
