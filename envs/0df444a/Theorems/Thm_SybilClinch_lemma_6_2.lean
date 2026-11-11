-- Prove2me | Theorems.Thm_SybilClinch_lemma_6_2
-- name    : SybilClinch.lemma_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:45:04.04992+00:00
-- url     : https://prove2.me/theorems/bc1ba9ca-2173-4156-83b2-159336298173
-- title:
--   Lemma 6.2 — infinite bids admit finite truncation
-- statement:
--   Let $\widehat C$ be an admissible cost on $[0,\mathrm{cap})$ with initial clock price $p_\star$ (in particular either extended cost $\widetilde C_M$ or $\widetilde C^{\rm rev}_M$), consider a profile of nonnegative reports with values in $\mathbb R\cup\{+\infty\}$, let $B_0$ be the total initial budget of the auction, and set
--   $$z_B:=\widehat C^{-1}(B_0),\qquad P_B:=\widehat C'_+(z_B)<\infty .$$
--   Then the run terminates at a finite clock price; any value report above $P_B$ can be replaced by any other value above $P_B$, or by $+\infty$, without changing the outcome; and an identity with infinite clock value spends its entire budget.
--
--   Differences from the source:
--   - generalization: Ĉ either extended cost C̃_M or C̃^rev_M → any cost K with IsAdmissibleCost K pstar cap; reason: both extended costs are admissible costs by Lemma 6.1, and the proof uses only the chord identity and the right derivative of an admissible cost
--   - reading: continuous evolution by the primitive conditions (16)–(18) on event-free open intervals, on which the clock and state paths are absolutely continuous → IsRun: the event procedure is applied at every clock price; off Clinch the continuous part of dx_i has no mass; a clincher stays at the water level on a right neighbourhood of every price while active; no absolute-continuity requirement on the paths; reason: event prices may accumulate (lumps of an admissible target can be dense) and, for an admissible AMM whose right marginal ask is flat on a fat Cantor set, the sole-survivor path X = Z(p) is continuous but not absolutely continuous, so a literal AC requirement would admit no run; on event-free intervals with AC paths the two formulations coincide
--   - reading: the run terminates at a finite clock price → there exists a completed run (IsRun, whose terminal price is a real number); reason: a run is defined only through its completion; termination means a completed run exists
--   - reading: B0, the total initial budget in that auction → the sum of q_i over the identities admitted at the initial price (v_i ≥ p⋆); reason: every remaining identity initially has b_i = q_i, ineligible reports being removed (p.9)
--   - encoding: z_B := Ĉ^{-1}(B0), P_B := Ĉ'_+(z_B) < ∞ → z_B := sup{z ∈ [0, cap) : Ĉ z ≤ B0}, with the conclusions 0 ≤ z_B < cap, Ĉ z_B = B0 and right-differentiability at z_B; P_B := derivWithin Ĉ (Ici z_B) z_B; reason: a real-valued derivative is finite by type, so finiteness is expressed by z_B lying below the capacity and the right derivative existing
--   - encoding: without changing the outcome → every completed run of the original profile has a completed run of the modified profile with the same terminal allocations and payments; reason: runs are relational
-- source:
--   Zhang, Li, Shi, Zhang, Xia, Han, Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design, arXiv:2610.36629 (held copy sha256 93c5d05b…), §6.1, Lemma 6.2, p.28 (PDF p.30); footnote 2, p.27 (PDF p.29)

import Mathlib
import Definitions.Def_SybilClinch_IsRun
import Definitions.Def_SybilClinch_IsAdmissibleCost
import Definitions.Def_SybilClinch_chordMech
import Definitions.Def_SybilClinch_OneSidedProfile_Valid

set_option autoImplicit false

open Filter Topology Set MeasureTheory

namespace SybilClinch

/-- Zhang, Li, Shi, Zhang, Xia, Han, *Sybil-Proofness of Generalized Adaptive Clinching and Implications for Blockchain Mechanism Design*, arXiv:2610.36629 (held copy sha256 93c5d05b…), §6.1, Lemma 6.2 (Infinite bids admit finite truncation), printed p.28 (PDF p.30), with
footnote 2, printed p.27 (PDF p.29).

Let `Ĉ` be an extended cost, `p⋆` its initial clock price and `B₀` the total initial budget in the
auction. Set `z_B := Ĉ⁻¹(B₀)` and `P_B := Ĉ′₊(z_B) < ∞`. The run terminates at a finite clock price;
any value report above `P_B` can be replaced by any other value above `P_B`, or by `+∞`, without
changing the outcome; in particular an identity with infinite clock value spends its entire budget.

**Formalization Note.** Generalized from the two extended costs `C̃_M`, `C̃^rev_M` to any admissible
cost (they are admissible costs by Lemma 6.1, and the proof uses only these properties). Values
lie in `WithTop ℝ`. `B₀` sums the budgets of the identities admitted at `p⋆` (`vᵢ ≥ p⋆`). `z_B` is
written as `sup {z ∈ [0, cap) : Ĉ z ≤ B₀}`; the lemma asserts it is `Ĉ⁻¹(B₀)` (`Ĉ z_B = B₀`),
below the capacity, with a right derivative there. "Terminates" is the existence of a completed run
(a run has a finite terminal price by definition); "without changing the outcome" means every run
of one profile has a run of the other with the same terminal allocations and payments. -/
theorem lemma_6_2 (K : ℝ → ℝ) (pstar cap : ℝ) (hK : IsAdmissibleCost K pstar cap)
    (P : OneSidedProfile) (hP : P.Valid) :
    let B₀ := ∑ i ∈ P.ids.filter (fun i => (pstar : WithTop ℝ) ≤ P.v i), P.q i
    let zB := sSup {z : ℝ | 0 ≤ z ∧ z < cap ∧ K z ≤ B₀}
    let PB := derivWithin K (Ici zB) zB
    (0 ≤ zB ∧ zB < cap ∧ K zB = B₀ ∧ DifferentiableWithinAt ℝ K (Ici zB) zB) ∧
    (∃ R : Run, IsRun (chordMech K pstar cap) P R) ∧
    (∀ v' : ℕ → WithTop ℝ,
      (∀ i ∈ P.ids, v' i = P.v i ∨ ((PB : WithTop ℝ) < P.v i ∧ (PB : WithTop ℝ) < v' i)) →
      ∀ R : Run, IsRun (chordMech K pstar cap) P R →
        ∃ R' : Run, IsRun (chordMech K pstar cap) ⟨P.ids, v', P.q⟩ R' ∧
          ∀ i ∈ P.ids, R'.x i R'.pf = R.x i R.pf ∧
            R'.pay (chordMech K pstar cap) i R'.pf = R.pay (chordMech K pstar cap) i R.pf) ∧
    (∀ R : Run, IsRun (chordMech K pstar cap) P R → ∀ i ∈ P.ids, P.v i = ⊤ →
      R.pay (chordMech K pstar cap) i R.pf = P.q i) := by sorry

end SybilClinch
