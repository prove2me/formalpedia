-- Prove2me | Theorems.Thm_WhitneyMatroid_Components_exists_circuit_meeting_both
-- name    : WhitneyMatroid.Components.exists_circuit_meeting_both
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T04:28:59.680648+00:00
-- url     : https://prove2.me/theorems/edae1443-cea8-4249-8cd5-f27e1730edb8
-- title:
--   Lemma 9 — a non-separable union of two disjoint parts has a circuit meeting both
-- statement:
--   Let $M$ be a finite matroid on a ground set $E$, and let $M_1, M_2\subseteq E$ be disjoint, each containing at least one element, such that $M_1+M_2$ is non-separable. Then there is a circuit $P$ of $M$ with
--
--   $$
--   P\subseteq M_1+M_2,\qquad P\cap M_1\neq\emptyset,\qquad P\cap M_2\neq\emptyset .
--   $$
--
--   This lemma converts the rank-defined notion of non-separability into the existence of circuits crossing any division; it is used in the proofs of Theorems 17, 18 and 19.
--
--   **Formalization Note** Whitney's matroid $M = M_1+M_2$ is here the submatroid $M_1\cup M_2$ of an ambient finite matroid; "a circuit $P$ in $M$" is a circuit of the ambient matroid contained in $M_1\cup M_2$.
-- source:
--   Whitney, On the Abstract Properties of Linear Dependence, Amer. J. Math. 57 (1935), p. 520, Lemma 9

import Mathlib
import Definitions.Def_WhitneyMatroid_Components_IsSeparable

namespace WhitneyMatroid.Components

theorem exists_circuit_meeting_both {α : Type*} (M : Matroid α) [M.Finite]
    (M₁ M₂ : Set α) (hM : IsNonSeparable M (M₁ ∪ M₂))
    (h₁ : M₁.Nonempty) (h₂ : M₂.Nonempty) (hdisj : Disjoint M₁ M₂) :
    ∃ P : Set α, M.IsCircuit P ∧ P ⊆ M₁ ∪ M₂ ∧ (P ∩ M₁).Nonempty ∧ (P ∩ M₂).Nonempty := by sorry

end WhitneyMatroid.Components
