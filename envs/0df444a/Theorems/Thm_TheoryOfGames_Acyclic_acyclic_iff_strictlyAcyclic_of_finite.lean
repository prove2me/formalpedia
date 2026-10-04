-- Prove2me | Theorems.Thm_TheoryOfGames_Acyclic_acyclic_iff_strictlyAcyclic_of_finite
-- name    : TheoryOfGames.Acyclic.acyclic_iff_strictlyAcyclic_of_finite
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T05:55:49.988449+00:00
-- url     : https://prove2.me/theorems/1dd549ee-2111-4c24-8da6-6276c4a45ad7
-- title:
--   (65:O:c) — strict acyclicity implies acyclicity, and the two coincide for finite D
-- statement:
--   Let $D$ be an arbitrary set and $\mathcal S$ an arbitrary relation on $D$. Then
--
--   1. if $\mathcal S$ is strictly acyclic (condition $(A_\infty)$), it is acyclic (all conditions $(A_1), (A_2), \dots$);
--   2. if $D$ is finite, $\mathcal S$ is acyclic if and only if it is strictly acyclic.
--
--   $$\text{strictly acyclic} \implies \text{acyclic}, \qquad D \text{ finite} \implies (\text{acyclic} \iff \text{strictly acyclic}).$$
--
--   This is why the standing hypothesis of 65.7 can be read either as acyclicity or as strict acyclicity, i.e. as (65:K), when $D$ is finite. The first part is also stated separately as (65:L).
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 597, 65.6.3, (65:O:c); p. 595, (65:L)

import Mathlib
import Definitions.Def_TheoryOfGames_Acyclic_Acyclicity

namespace TheoryOfGames.Acyclic

/-- (65:O:c), p. 597: strict acyclicity implies acyclicity for all `D`, but it is equivalent to
it for finite `D`. -/
theorem acyclic_iff_strictlyAcyclic_of_finite {α : Type*} (D : Set α) (S : α → α → Prop) :
    (IsStrictlyAcyclic D S → IsAcyclic D S) ∧
      (D.Finite → (IsAcyclic D S ↔ IsStrictlyAcyclic D S)) := by sorry

end TheoryOfGames.Acyclic
