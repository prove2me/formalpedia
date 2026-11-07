-- Prove2me | Theorems.Thm_PolygonPack_lemma_C_7
-- name    : PolygonPack.lemma_C_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:54:57.183227+00:00
-- url     : https://prove2.me/theorems/a3d91bf9-eca4-478a-882b-fdfe6e466ad1
-- title:
--   Lemma C.7 — prefix selection with an initial offset
-- statement:
--   Let heights $h_i>0$, capacities $C_i>0$ nondecreasing in $i$, profits $\pi_i\ge0$, $z_0\ge0$ and $0<\sigma<1$ satisfy $h_i\le cC_i$ and $2z_0/C_k+2c\le\sigma$ for all $k$.
--
--   1. There are a set $S$, a track assignment into two tracks and start times such that each selected job starts at or after $z_0$, finishes by $C_k/2$, and does not overlap another job on its track, and such that for every $\alpha\ge1$ and every subset $S'$ with $\sum_{i\in S',\,i\le k}h_i\le\alpha C_k$ for all $k$,
--   $$
--   \frac{1-\sigma}\alpha\,\pi(S')\le\pi(S).
--   $$
--   2. For rational $z_0,\sigma$, a polynomial-time machine computes such a selection from the rational data $(h_i,C_i,\pi_i)$.
--
--   The selection does not depend on the comparison subset or on $\alpha$, which is what lets an algorithm use it without knowing the comparison packing.
--
--   Differences from the source:
--   - generalization: all eligible enclosures satisfy the span inequalities of Lemma C.1 → no such hypothesis, on abstract data (h, C, π); reason: the proof uses them only to realize the tracks as a packing, by Lemma C.1
--   - reading: two tracks can be constructed → one selection before the comparison subset and α; reason: p.37: "without requiring the algorithm to know the comparison subset"
--   - reading: the rational version of the lemma applies, by standard rational linear programming → a clause with one machine for fixed rational z0 and σ, correct for every c; reason: p.38 and p.50 say this; the algorithm does not read c
--   - encoding: a feasible comparison subset of profit W → every subset S' with the prefix bound for that α; reason: the paper's feasibility is used only through this bound here
--   - reading: polynomial time in the total binary encoding length → Nonempty (Turing.TM2ComputableInPolyTime …) on the fixed binary encoders; reason: p.13 names this measure; the paper fixes no machine model
-- source:
--   Khan, Mathur, Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons, STOC 2027 submission (manuscript sha256 7a527fb3…), Lemma C.7, p.37; rational version, p.38 and p.50

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_PolygonPack_encInstance
import Definitions.Def_PolygonPack_IsTwoTrackSelection

namespace PolygonPack

/-- **Lemma C.7 (Prefix selection with an initial offset).** Khan, Mathur, *Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons*, STOC 2027 submission (manuscript sha256 7a527fb3…), p.37. "Suppose all eligible enclosures satisfy the span inequalities of Lemma C.1. Suppose also that a
feasible comparison subset has profit W, and its total thickness in every input prefix 1, . . . , k is at most αC_k, where α ≥ 1. Fix 0 < σ < 1 and suppose
2z0/C_k + 2c ≤ σ for every eligible k. Then two tracks starting at z0 can be constructed with total profit at least (1 − σ)W/α, such that every selected job k finishes
by its deadline C_k/2."

Two clauses. For real data the tracks exist **before** the comparison subset and `α`: p.37, "without requiring the algorithm to know the comparison subset". For rational
data a polynomial-time machine, fixed once `z0` and `σ` are, computes them: p.38, "The rational version of the lemma applies", and p.50, "Standard rational linear
programming".

**Formalization Note.** This is the abstract form on the data `(h, C, π)` of the preamble on p.37: `0 < h_i ≤ cC_i`, `C` positive and nondecreasing. The span inequalities are used
only to realize the tracks as a packing, by Lemma C.1, so they are not hypotheses here. The output lists the selected jobs with their track and rational start time. -/
theorem lemma_C_7 :
    (∀ (m : ℕ) (c : ℝ) (h π C : Fin m → ℝ) (z0 σ : ℝ), IsTrackData c h π C z0 σ →
      ∃ (S : Finset (Fin m)) (track : Fin m → Fin 2) (start : Fin m → ℝ),
        IsTwoTrackSelection h C z0 S track start ∧ DominatesPrefix h π C σ S) ∧
    (∀ z0 σ : ℚ, 0 ≤ z0 → 0 < σ → σ < 1 →
      ∃ f : List (ℚ × ℚ × ℚ) → List (ℕ × Bool × ℚ),
        Nonempty (Turing.TM2ComputableInPolyTime encJobs encTrackOut f) ∧
        ∀ (c : ℝ) (jobs : List (ℚ × ℚ × ℚ)),
          IsTrackData c (fun i => (((jobs.get i).1 : ℚ) : ℝ)) (fun i => (((jobs.get i).2.2 : ℚ) : ℝ))
              (fun i => (((jobs.get i).2.1 : ℚ) : ℝ)) (z0 : ℝ) (σ : ℝ) →
            ∃ (S : Finset (Fin jobs.length)) (track : Fin jobs.length → Fin 2) (start : Fin jobs.length → ℝ),
              TrackOutRealizes (f jobs) S track start ∧
              IsTwoTrackSelection (fun i => (((jobs.get i).1 : ℚ) : ℝ)) (fun i => (((jobs.get i).2.1 : ℚ) : ℝ))
                (z0 : ℝ) S track start ∧
              DominatesPrefix (fun i => (((jobs.get i).1 : ℚ) : ℝ)) (fun i => (((jobs.get i).2.2 : ℚ) : ℝ))
                (fun i => (((jobs.get i).2.1 : ℚ) : ℝ)) (σ : ℝ) S) := by sorry

end PolygonPack
