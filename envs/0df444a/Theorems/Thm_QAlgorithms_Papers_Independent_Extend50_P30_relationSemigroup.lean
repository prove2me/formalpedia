-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P30_relationSemigroup
-- name    : QAlgorithms.Papers.Independent.Extend50.P30.relationSemigroup
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:17:21.886989+00:00
-- url     : https://prove2.me/theorems/c7e9b414-d3af-450b-9360-8ba438955965
-- title:
--   Scalar-twisted semigroup of relations
-- statement:
--   Let $d$ be prime and $t\geq1$. Relational composition of stochastic Lagrangians is again a stochastic Lagrangian, is associative, and has the diagonal relation as identity. For arbitrary $T_1,T_2$, set $K=(T_1)_{RD}\cap(T_2)_{LD}$, the space of differences between intermediate solutions. Its cardinality gives the scalar in the physical tensor multiplication law.
--
--   $$
--   R(T_1)R(T_2)=|K|^nR(T_1\circ T_2)=d^{n\dim K}R(T_1\circ T_2).
--   $$
--
--   This gives the source's scalar-twisted semigroup of relations in the fixed computational-basis and phase conventions.
--
--   **Formalization Note** Pure states carry norm one; stabilizer averages use density matrices to discard global phases. All finite tensor indices are explicitly ordered by copy, then physical qudit.
-- source:
--   Schur-Weyl Duality for the Clifford Group with Applications: Property Testing, a Robust Hudson Theorem, and de Finetti Representations, arXiv:1712.08628v3, PDF p. 40, semigroup

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P30

noncomputable section

open scoped BigOperators ComplexConjugate Matrix

namespace QAlgorithms.Papers.Independent.Extend50.P30

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

open QAlgorithms.Papers.Independent.Gap20.P06 (ketBra)

attribute [local instance] Classical.propDecidable

/-- PDF pp.40--41: associative relational semigroup with its scalar-twisted multiplication.
For general relations the fiber is rightDefect(T1) intersect leftDefect(T2). -/
theorem relationSemigroup (d t : ℕ) [NeZero d] [Fact (Nat.Prime d)] (ht : 1 ≤ t) :
    (∀ A B : Lagrangian d t, IsStochasticLagrangian (composeRelation A.val B.val) ∧
      ((↑(composeRelation A.val B.val) : Set (ResidueRegister d t × ResidueRegister d t)) = {z | ∃ y, (z.1, y) ∈ A.val ∧ (y, z.2) ∈ B.val})) ∧
    (∀ A B C : Lagrangian d t,
      composeRelation (composeRelation A.val B.val) C.val = composeRelation A.val (composeRelation B.val C.val)) ∧
    (∀ A : Lagrangian d t,
      composeRelation (graphRelation (1 : Matrix (Fin t) (Fin t) (ZMod d))) A.val = A.val ∧
      composeRelation A.val (graphRelation (1 : Matrix (Fin t) (Fin t) (ZMod d))) = A.val) ∧
    (∀ n : ℕ, ∀ A B : Lagrangian d t,
      tensorRelation n A.val * tensorRelation n B.val =
        ((Nat.card ↥(rightDefect A.val ⊓ leftDefect B.val) : ℂ) ^ n) •
          tensorRelation n (composeRelation A.val B.val) ∧
      tensorRelation n A.val * tensorRelation n B.val =
        ((d : ℂ) ^ (n * Module.finrank (ZMod d) ↥(rightDefect A.val ⊓ leftDefect B.val))) •
          tensorRelation n (composeRelation A.val B.val)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P30

end
