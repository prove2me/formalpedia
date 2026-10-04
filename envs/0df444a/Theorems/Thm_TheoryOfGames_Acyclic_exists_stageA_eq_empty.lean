-- Prove2me | Theorems.Thm_TheoryOfGames_Acyclic_exists_stageA_eq_empty
-- name    : TheoryOfGames.Acyclic.exists_stageA_eq_empty
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T06:00:04.969539+00:00
-- url     : https://prove2.me/theorems/d23b3ffd-cc14-434c-9c22-6d03ee79e3ac
-- title:
--   (65:S) — the construction of 65.7.1 reaches A_i = ⊖
-- statement:
--   Assume the standing hypotheses of 65.7.1: $D$ is finite and $\mathcal S$ is acyclic on $D$ (for finite $D$ equivalently strictly acyclic, i.e. property (65:K)). Let $A_1 = D, A_2, A_3, \dots$ be the sets of the inductive construction of 65.7.1 ($B_i = A_i^m$, $C_i$ the elements of $A_i$ dominated by an element of $B_i$, $A_{i+1} = A_i - B_i - C_i$). Then
--
--   $$\exists\, i:\ A_i = \ominus.$$
--
--   The smallest such $i$ is the index $i_0$ of (65:T), which makes $V_0 = B_1 \cup \cdots \cup B_{i_0-1}$ of (65:2) well defined as a finite union.
--
--   **Formalization Note** The Lean stages are indexed from $0$ (`stageA D S 0 = D` is $A_1$); the statement is the existence of some index and so is unaffected by the shift.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 598, 65.7.1, (65:S)

import Mathlib
import Definitions.Def_TheoryOfGames_Acyclic_Solution
import Definitions.Def_TheoryOfGames_Acyclic_Acyclicity
import Definitions.Def_TheoryOfGames_Acyclic_Construction

namespace TheoryOfGames.Acyclic

/-- (65:S), p. 598: under the standing assumptions of 65.7.1 — `D` finite and `S` acyclic on `D`
(equivalently, for finite `D`, strictly acyclic, i.e. (65:K)) — there exists an `i` with
`A_i = ⊖`, for the sets `A_i` of the construction of 65.7.1. -/
theorem exists_stageA_eq_empty {α : Type*} (D : Set α) (S : α → α → Prop)
    (hD : D.Finite) (hS : IsAcyclic D S) :
    ∃ k : ℕ, stageA D S k = ∅ := by sorry

end TheoryOfGames.Acyclic
