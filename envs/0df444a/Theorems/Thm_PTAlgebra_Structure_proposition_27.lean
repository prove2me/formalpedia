-- Prove2me | Theorems.Thm_PTAlgebra_Structure_proposition_27
-- name    : PTAlgebra.Structure.proposition_27
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:32:21.209706+00:00
-- url     : https://prove2.me/theorems/c7f17475-363f-4301-9a1a-070dff3ca3d4
-- title:
--   Proposition 27, p. 7 — complementary annihilating ideals
-- statement:
--   Let $A=A_n^{t_n}(d)$ and let $M$ be the complex span of the partially transposed permutation operators that move the final position. Proposition 27 asserts that $M$ has a two-sided unit $e$ and
--   $$M=eAe,\qquad S=(1-e)A(1-e),\qquad A=M\oplus S,\qquad MS=SM=0.$$
--   Both $M$ and $S$ are two-sided ideals of $A$, and $e$ belongs to $M$. The direct sum has zero intersection and spans $A$.
--
--   This isolates the complementary ideal whose matrix components are classified in Theorem 30(b).
--
--   **Formalization Note** Corners are represented as complex spans of $eae$ with $a\in A$. The theorem allows $n=2$ and requires $d\ge1$.
-- source:
--   Mozrzymas, Horodecki, Studziński, Structure and properties of the algebra of partially transposed permutation operators, arXiv:1308.2653v3, p. 7, sentence before and Proposition 27

import Mathlib
import Definitions.Def_PTAlgebra_Structure_Defs

namespace PTAlgebra.Structure

open PTCommutant.OperatorBasis

/-- Proposition 27, p. 7, including the unit of `M` stated immediately before it. -/
theorem proposition_27 (d m : ℕ) (hd : 1 ≤ d) :
    ∃ (e : Op d (m + 2)) (S : Submodule ℂ (Op d (m + 2))),
      e ∈ algM d m ∧
      (∀ x ∈ algM d m, e * x = x ∧ x * e = x) ∧
      algM d m = corner e (algA d m) ∧
      S = corner (1 - e) (algA d m) ∧
      IsIdealOf (algM d m) (algA d m) ∧ IsIdealOf S (algA d m) ∧
      algM d m ⊓ S = ⊥ ∧ algM d m ⊔ S = algA d m ∧
      (∀ x ∈ algM d m, ∀ y ∈ S, x * y = 0 ∧ y * x = 0) := by sorry

end PTAlgebra.Structure
