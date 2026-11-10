-- Prove2me | Theorems.Thm_WeightedSetCoverWorstCase_Dynamic_lemma_13_1
-- name    : WeightedSetCoverWorstCase.Dynamic.lemma_13_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:30:02.337557+00:00
-- url     : https://prove2.me/theorems/d66077c0-c108-49aa-9979-49dfcba1b830
-- title:
--   Lemma 13.1 — an implementation of the algorithm with worst-case update time $\tilde O(f)$
-- statement:
--   For every $0<\varepsilon<1/10$ there is a deterministic program $P$ for the real RAM (literals rational or $\varepsilon$, no coins) such that for every aspect exponent $d$ there are $K$ and $b$ with: for every instance with $c(s)\le\max(2,n)^dc(s')$, every initial live set $U_0$ and every legal update sequence, preprocessing halts; every update call halts within $Kf(1+\log\max(1,fn))^b$ steps; and $P$ implements the algorithm — there is a run of the algorithm (parameter $\varepsilon$) on the insertions of $U_0$ in increasing order followed by the updates that reaches an idle state after each update, and at every idle state after the insertions of $U_0$ the machine's maintained set family equals the deduplicated output $C^F+C^B$ of the run.
--
--   Differences from the source:
--   - encoding: an implementation of our algorithm → a program of the online real-RAM protocol whose output after preprocessing and after each update equals the deduplicated output of some run of the algorithm (Step ε) at the corresponding idle state; reason: an implementation is a program computing the algorithm's output; free choices of the algorithm may be resolved by the program
--   - reading: an arbitrary initial live set U₀ (no initialization procedure is given) → the algorithm run inserts the elements of U₀ in increasing order before the updates; preprocessing time is not bounded; reason: the paper gives no initialization; Õ(f) is claimed per time step
--   - encoding: worst-case update time Õ(f) per time step, under C ≤ poly(n) → for each aspect exponent d, ∃ K b with every update call halting within K f (1 + log max(1, f n))^b executed instructions; reason: Õ hides polylogarithmic factors; the constants may depend on ε and d but not on the instance or the sequence
--   - generalization: an implementation with exact arithmetic (machine constants unrestricted) → the program's real literals are rational or ε, and it has no coin instruction; reason: a stronger claim: such a program is in particular a deterministic implementation
--   - reading: 0 < ε < 1/10 is a sufficiently small constant (§6.1) → every ε with 0 < ε < 1/10; reason: the stronger of the two readings
--   - generalization: a finite family S of subsets of the base universe → a finite indexed family of subsets, possibly with repeated underlying subsets; reason: an injective enumeration gives every source instance; positive-cost duplicates do not invalidate the counting, covering, or operational bounds
-- source:
--   Bhattacharya, Cen, Farokhnejad and Panigrahi (2026), Fully Dynamic Weighted Set Cover: Worst-Case Recourse and Update Time, STOC 2027 submission, supplied PDF sha256 28a86be41fbea2451c118c89c7385500105ced4b59ab5e66110721ebf0909337, Lemma 13.1, p. 60 (PDF 63)

import Mathlib
import Definitions.Def_DynSetCover_Instance
import Definitions.Def_WeightedSetCoverWorstCase_Dynamic_Problem
import Definitions.Def_WeightedSetCoverWorstCase_Dynamic_Algorithm
import Definitions.Def_ClusterDecomp_Machine
import Definitions.Def_WeightedSetCoverWorstCase_Dynamic_Machine

open ClusterDecomp

namespace WeightedSetCoverWorstCase.Dynamic

theorem lemma_13_1 (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 10) :
    ∃ P : Program, AdmissibleWith [ε] P ∧ NoCoin P ∧
    ∀ d : ℕ, ∃ K : ℝ, ∃ b : ℕ,
    ∀ (inst : Instance), AspectBound inst d →
    ∀ (U₀ : Finset (Fin inst.u)) (ups : List (Update inst.u)), LegalSeq U₀ ups →
      (∃ T, HaltsWithin P (scInit inst U₀) T) ∧
      (∀ (i : ℕ) (hi : i < ups.length), ∃ T : ℕ,
        (T : ℝ) ≤ K * (inst.freq : ℝ) * (1 + Real.log (max 1 ((inst.freq * inst.u : ℕ) : ℝ))) ^ b ∧
        HaltsWithin P (callState (scAfter P inst U₀ (ups.take i)) (encUpd (ups.get ⟨i, hi⟩))) T) ∧
      ∃ (c : ℕ → AlgState inst) (ev : ℕ → Ev),
        IsRun inst ε ((U₀.sort (· ≤ ·)).map (fun x => DynSetCover.Upd.ins x) ++ ups) c ev ∧
        (∀ i ≤ ups.length, ∃ N, (c N).mode = Mode.idle ∧ (c N).rest.length = ups.length - i) ∧
        ∀ N : ℕ, (c N).mode = Mode.idle → (c N).rest.length ≤ ups.length →
          outFamily inst (scAfter P inst U₀ (ups.take (ups.length - (c N).rest.length))) =
            copiesSets (c N).outCopies := by sorry

end WeightedSetCoverWorstCase.Dynamic
