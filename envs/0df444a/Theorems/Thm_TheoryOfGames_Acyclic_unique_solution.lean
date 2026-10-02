-- Prove2me | Theorems.Thm_TheoryOfGames_Acyclic_unique_solution
-- name    : TheoryOfGames.Acyclic.unique_solution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T06:11:22.215123+00:00
-- url     : https://prove2.me/theorems/9c57955d-7d38-43c6-9805-66d639b02aa2
-- title:
--   (65:X) — an acyclic relation on a finite set has exactly one solution, V₀
-- statement:
--   Let $D$ be a finite set and $\mathcal S$ an acyclic relation on $D$ (conditions $(A_1), (A_2), \dots$ of (65:D:c); for finite $D$ equivalently strictly acyclic, i.e. every non-empty subset of $D$ has maxima). These are the standing hypotheses of 65.7.1. Then there exists one and only one solution in $D$ for $\mathcal S$, namely the set $V_0 = B_1 \cup \cdots \cup B_{i_0-1}$ of (65:2), obtained from the inductive construction of 65.7.1. Precisely:
--
--   $$\exists!\, V \text{ with } V = \{y \in D : x\mathcal S y \text{ for no } x \in V\}, \qquad\text{and}\qquad V \text{ is a solution} \iff V = V_0 .$$
--
--   In graph-theoretic terms: a finite directed graph without directed cycles has exactly one kernel (an independent set that dominates every vertex outside it). The theorem generalizes the complete-ordering case (65:E)–(65:F) and the partial-ordering case (65:H)–(65:I) of §65.
--
--   **Formalization Note** Uniqueness ranges over all sets `V : Set α`, not over a subtype; the solution equation itself forces $V \subseteq D$. `V0 D S` is the union of all stages $B_i$ of 65.7.1 (equal to $B_1 \cup \cdots \cup B_{i_0-1}$). The infinite case is not stated: the book leaves it open (65.7.1, (65:Y), (65:9)).
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 600, 65.7.2, (65:X); standing hypotheses p. 598, 65.7.1

import Mathlib
import Definitions.Def_TheoryOfGames_Acyclic_Solution
import Definitions.Def_TheoryOfGames_Acyclic_Acyclicity
import Definitions.Def_TheoryOfGames_Acyclic_Construction

namespace TheoryOfGames.Acyclic

/-- (65:X), p. 600: under the standing assumptions of 65.7.1 (`D` finite, `S` acyclic on `D`),
there exists one and only one solution (in `D` for `S`), the `V₀` of (65:2): uniqueness is
over all sets `V : Set α`, and a set is a solution exactly when it equals `V₀`. -/
theorem unique_solution {α : Type*} (D : Set α) (S : α → α → Prop)
    (hD : D.Finite) (hS : IsAcyclic D S) :
    (∃! V : Set α, IsSolution D S V) ∧ ∀ V : Set α, IsSolution D S V ↔ V = V0 D S := by sorry

end TheoryOfGames.Acyclic
