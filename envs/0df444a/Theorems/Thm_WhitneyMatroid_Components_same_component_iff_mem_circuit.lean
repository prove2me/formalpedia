-- Prove2me | Theorems.Thm_WhitneyMatroid_Components_same_component_iff_mem_circuit
-- name    : WhitneyMatroid.Components.same_component_iff_mem_circuit
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T04:50:28.891824+00:00
-- url     : https://prove2.me/theorems/41febb3c-9bc2-44c5-9cb8-1a914483042e
-- title:
--   Theorem 19 — two elements share a component iff some circuit contains both
-- statement:
--   Let $M$ be a finite matroid on a ground set $E$, and let $e_1, e_2\in E$ be two distinct elements. Then $e_1$ and $e_2$ lie in the same component of $M$ if and only if they are contained in a common circuit:
--
--   $$
--   \exists K \text{ component of } M,\ e_1,e_2\in K \iff \exists P \text{ circuit of } M,\ e_1,e_2\in P .
--   $$
--
--   Components are defined through the rank function (maximal non-separable parts), while circuits are minimal dependent sets; the theorem identifies the rank-theoretic decomposition with the relation "lie on a common circuit". In particular that relation is an equivalence relation on distinct elements, and, as Whitney notes, König's "Glieder" of a graph are the same as the components of its matroid.
--
--   **Formalization Note** The elements are assumed distinct ($e_1\neq e_2$), which Whitney's "the elements $e_1$ and $e_2$" leaves tacit: for $e_1=e_2$ a coloop forms its own component but lies on no circuit. Components are the rank-defined `IsComponent` (not the classes of the circuit relation, which would make the theorem a tautology); circuits are Mathlib's `Matroid.IsCircuit`.
-- source:
--   Whitney, On the Abstract Properties of Linear Dependence, Amer. J. Math. 57 (1935), p. 521, Theorem 19

import Mathlib
import Definitions.Def_WhitneyMatroid_Components_IsSeparable
import Definitions.Def_WhitneyMatroid_Components_IsComponent

namespace WhitneyMatroid.Components

theorem same_component_iff_mem_circuit {α : Type*} (M : Matroid α) [M.Finite]
    (e₁ e₂ : α) (he₁ : e₁ ∈ M.E) (he₂ : e₂ ∈ M.E) (hne : e₁ ≠ e₂) :
    (∃ K : Set α, IsComponent M K ∧ e₁ ∈ K ∧ e₂ ∈ K) ↔
      ∃ P : Set α, M.IsCircuit P ∧ e₁ ∈ P ∧ e₂ ∈ P := by sorry

end WhitneyMatroid.Components
