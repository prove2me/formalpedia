-- Prove2me | Theorems.Thm_WhitneyMatroid_Binary_isCircuit_iff_minimal_nonnull_cycle
-- name    : WhitneyMatroid.Binary.isCircuit_iff_minimal_nonnull_cycle
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T05:01:40.794787+00:00
-- url     : https://prove2.me/theorems/9e950e61-5828-4d5e-a4a7-3db8e1c0f5db
-- title:
--   Theorem 33 — under (C*), a circuit is a minimal non-null cycle, and conversely
-- statement:
--   Let $M$ be a matroid on a finite set of elements satisfying Postulate (C\*). Then a set $C$ is a circuit of $M$ if and only if it is a **minimal non-null cycle**: $C$ is a cycle, $C \neq \emptyset$, and
--
--   $$D \text{ a non-null cycle},\ D \subseteq C \implies D = C.$$
--
--   This identifies the circuits of a (C\*)-matroid from its cycles alone, which is how Theorem 36 defines the circuits of the matroid it constructs and how Theorem 35 recovers all circuits from a fundamental set.
--
--   **Formalization Note** Cycles are taken with respect to the circuit family `{C | M.IsCircuit C}` of the Mathlib matroid `M`; the ground type is finite.
-- source:
--   Whitney, On the Abstract Properties of Linear Dependence, Amer. J. Math. 57 (1935), p. 531, Theorem 33

import Mathlib
import Definitions.Def_WhitneyMatroid_Binary_Cycles

namespace WhitneyMatroid.Binary

/-- Theorem 33 (Appendix, p. 531). In a matroid `M` satisfying (C*), a circuit is a minimal
non-null cycle, and conversely. -/
theorem isCircuit_iff_minimal_nonnull_cycle {α : Type*} [Finite α] (M : Matroid α)
    (hC : SatisfiesCStar {C | M.IsCircuit C}) (C : Set α) :
    M.IsCircuit C ↔
      (IsCycleOf {C | M.IsCircuit C} C ∧ C.Nonempty ∧
        ∀ D : Set α, IsCycleOf {C | M.IsCircuit C} D → D.Nonempty → D ⊆ C → D = C) := by sorry

end WhitneyMatroid.Binary
