-- Prove2me | Theorems.Thm_TheoryOfGames_Acyclic_hasMaximaProperty_iff_strictlyAcyclic
-- name    : TheoryOfGames.Acyclic.hasMaximaProperty_iff_strictlyAcyclic
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T05:57:26.256183+00:00
-- url     : https://prove2.me/theorems/23bda98a-8f57-4213-834f-7eafc7d96d28
-- title:
--   (65:P) — (65:K) is equivalent to strict acyclicity
-- statement:
--   Let $D$ be an arbitrary set and $\mathcal S$ an arbitrary relation on $D$ (65.6.2 drops every restriction on $D$ and $\mathcal S$). Then
--
--   $$\bigl(\forall E \subseteq D:\ E \neq \ominus \implies E^m \neq \ominus\bigr) \iff \mathcal S \text{ is strictly acyclic},$$
--
--   where $E^m$ is the set of maxima of $E$ (elements of $E$ dominated by no element of $E$) and strict acyclicity means that there is no sequence $x_0, x_1, x_2, \dots$ in $D$ with $x_1\mathcal S x_0,\ x_2\mathcal S x_1,\ x_3\mathcal S x_2, \dots$.
--
--   Property (65:K) is the hypothesis used in the construction of the solution in 65.7 (its only use is to guarantee $B_i = A_i^m \ne \ominus$); (65:P) identifies it with a condition on chains. When $\mathcal S$ is read as "before", this is the familiar equivalence between well-foundedness and the absence of infinite descending chains.
-- source:
--   von Neumann & Morgenstern, Theory of Games and Economic Behavior (60th-anniversary ed., Princeton 2007), p. 597, 65.6.3, (65:P); p. 595, (65:K)

import Mathlib
import Definitions.Def_TheoryOfGames_Acyclic_Solution
import Definitions.Def_TheoryOfGames_Acyclic_Acyclicity

namespace TheoryOfGames.Acyclic

/-- (65:P), p. 597: for an arbitrary set `D` and an arbitrary relation `S` (65.6.2 drops all
restrictions on `D` and `S`), the property (65:K) — every non-empty `E ⊆ D` possesses maxima —
is equivalent to strict acyclicity. -/
theorem hasMaximaProperty_iff_strictlyAcyclic {α : Type*} (D : Set α) (S : α → α → Prop) :
    HasMaximaProperty D S ↔ IsStrictlyAcyclic D S := by sorry

end TheoryOfGames.Acyclic
