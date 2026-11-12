-- Prove2me | Theorems.Thm_QPVEntanglement_proposition_1
-- name    : QPVEntanglement.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T08:39:25.78869+00:00
-- url     : https://prove2.me/theorems/7c2c848a-c85f-4726-a069-2267df48ae41
-- title:
--   Proposition 1 — reduction to a nonoverlapping execution
-- statement:
--   This item is stated in the **operator-requested pinned-down model** of the paper's adversary model (§4, pp.28–29): the paper defines its coalitions only operationally, so the mission fixes a precise model (choices P1–P14 of the mission description) and states the paper's result in it at full strength.
--
--   Consider the protocol with an admissible geometry and a schedule with slot spacing $\Delta>0$, and let $D=\max(d_0,d_1)$. Suppose a coalition with no station at the claimed location has quantum-register size $Q$ and succeeds with probability $p$. For every $\Delta^\star>\max\{\Delta,2D\}$, the execution with the same verifier and station locations, the same protocol actions and slot spacing $\Delta^\star$ (the stretched schedule of eq. (100)) has a coalition of quantum-register size $Q$ and success probability at least $p$. Moreover, within each round the slot intervals $[T^\star_{k,j}-D,\;T^\star_{k,j}+D]$ of the new execution are pairwise disjoint.
--
--   It lets the security proof assume non-overlapping slots.
--
--   Differences from the source:
--   - reading: adversarial coalition defined operationally (§4 Adversary Model, clauses 1–6, pp.28–29; protocol rules 1–5, pp.30–32) → `Coalition S`: finitely many stations at distinct positions, each with q a qubits and fixed-time events applying a view-dependent complete Kraus instrument and an absorb/launch action, causal w.r.t. the light cone; `acceptProb` and `size` as in the mission description (P5–P11); reason: operator-requested pinned-down model (OPERATOR_NOTE 2026-11-11); the paper's model is not precise enough to state as written
--   - generalization: claimed location 0, V0 = −L, V1 = R → every admissible geometry (v0, v1, x arbitrary, x strictly between); reason: the normalization is a translation and reflection; the general statement specializes to it
--   - encoding: the same verifier and adversary locations, the same protocol actions, slot spacing ∆⋆ → equal sets of station positions; the schedule `Schedule.stretch` of eq. (100); reason: the proof (p.72) defines the new execution by eq. (100); station positions are distinct, so equal position sets mean the same locations
--   - encoding: the consecutive slot intervals for the new execution are disjoint → all pairs of slot intervals within a round are disjoint; reason: the intervals are ordered by their centres, so consecutive disjointness and pairwise disjointness coincide
-- source:
--   Behera, Goyal, Breaking the Bounded Entanglement Barrier for Quantum Position Verification, arXiv:2609.39234 (sha256 bdf2928d…), Proposition 1, p.37; proof App. C.1, pp.72–74

import Mathlib
import Definitions.Def_QPVEntanglement_Coalition_size
import Definitions.Def_QPVEntanglement_Schedule_stretch

set_option autoImplicit false

namespace QPVEntanglement

/-- **Proposition 1 (Reduction to a Nonoverlapping Execution)**, p.37 (proof App. C.1,
pp.72–74), stated in the operator-requested pinned-down model of §4 (BRIEF P1–P14).
Behera–Goyal, arXiv:2609.39234 (sha256 bdf2928d…), Proposition 1, p.37.

For every geometry, schedule `S` with slot spacing `Δ > 0`, and coalition with no station at the
claimed location, of quantum-register size `Q` and success probability `p`: for every
`Δ⋆ > max{Δ, 2D}`, the execution with the same verifier and station locations, the same
protocol actions and slot spacing `Δ⋆` (the stretched schedule of eq. (100)) has a coalition of
quantum-register size `Q` and success probability at least `p`; moreover the slot intervals
`[T⋆_{k,j} − D, T⋆_{k,j} + D]` of each round are pairwise disjoint.

**Formalization Note.** "Same adversary locations" is equality of the sets of station
positions; the stretched schedule is `Schedule.stretch` (eq. (100) and the paragraph after it).
The geometry is general (`v₀, v₁, x` arbitrary with `x` strictly between), `D = max(d₀, d₁)`. -/
theorem proposition_1 (G : Geometry) (m RH s : ℕ) (S : Schedule G m RH s) (C : Coalition S)
    (hx : ∀ a, C.pos a ≠ G.x) (Δstar : ℝ) (hΔ : max S.Δ (2 * G.D) < Δstar) :
    ∃ Cstar : Coalition (S.stretch Δstar ((S.Δ_pos.trans_le (le_max_left _ _)).trans hΔ)),
      Set.range Cstar.pos = Set.range C.pos ∧ Cstar.size = C.size ∧
      C.acceptProb ≤ Cstar.acceptProb ∧
      ∀ (k : Fin m) (j j' : Fin s), j ≠ j' →
        Disjoint
          (Set.Icc ((S.stretch Δstar ((S.Δ_pos.trans_le (le_max_left _ _)).trans hΔ)).T k j - G.D)
            ((S.stretch Δstar ((S.Δ_pos.trans_le (le_max_left _ _)).trans hΔ)).T k j + G.D))
          (Set.Icc ((S.stretch Δstar ((S.Δ_pos.trans_le (le_max_left _ _)).trans hΔ)).T k j' - G.D)
            ((S.stretch Δstar ((S.Δ_pos.trans_le (le_max_left _ _)).trans hΔ)).T k j' + G.D)) := by sorry

end QPVEntanglement
