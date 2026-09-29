-- Prove2me | Theorems.Thm_Set_ncard_pairing_annihilator_mul_ncard_eq_ncard_mul_ncard_radical
-- name    : Set.ncard_pairing_annihilator_mul_ncard_eq_ncard_mul_ncard_radical
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/5035c975-11ea-5b37-9947-bb5fa164e089
-- title:
--   Annihilator count for a bimultiplicative pairing
-- statement:
--   Let $J$ and $J'$ be additive abelian groups and $L$ a field of characteristic zero. Let $A \subseteq J$ and $X' \subseteq J'$ be subsets, both assumed finite, both containing $0$ and closed under addition and under negation (so each is the underlying set of a finite subgroup, though no subgroup structure is assumed in the statement). Let $B : J \to J' \to L$ be an arbitrary function which is bimultiplicative on $A \times X'$ in the following sense: $B(a+a', y) = B(a,y)\,B(a',y)$ for all $a, a' \in A$ and $y \in X'$, and $B(a, y+y') = B(a,y)\,B(a,y')$ for all $a \in A$ and $y, y' \in X'$. Then the natural-number cardinalities (`Set.ncard`) satisfy
--   $$\#\{y \in X' : B(a,y) = 1 \text{ for all } a \in A\} \cdot \#A = \#X' \cdot \#\{a \in A : B(a,y) = 1 \text{ for all } y \in X'\};$$
--   that is, the annihilator of $A$ inside $X'$ and the radical of $B$ inside $A$ have cardinalities related by $\#\mathrm{Ann}_{X'}(A)\,\#A = \#X'\,\#\mathrm{rad}_A$. No perfectness of $B$ and no assumption that its values are roots of unity is needed.
--
--   This is the elementary counting identity underlying duality counts for pairings of finite abelian groups: the index of the annihilator of $A$ in $X'$ equals the index of the radical of $B$ in $A$. It is used in the project to compare cardinalities on the corner of a $p$-torsion group scheme via an abel–Jacobi pairing, and to deduce that all elements of a subgroup are annihilated by a pairing once the cardinality identity forces the annihilator to be everything.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Set_ncard_pairing_annihilator_mul_ncard_eq_ncard_mul_ncard_radical.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Set.ncard_pairing_annihilator_mul_ncard_eq_ncard_mul_ncard_radical
    {J J' : Type} [AddCommGroup J] [AddCommGroup J'] {L : Type} [Field L] [CharZero L]
    (A : Set J) (X' : Set J') (hA : A.Finite) (hX' : X'.Finite)
    (hA0 : (0 : J) ∈ A) (hAadd : ∀ x ∈ A, ∀ y ∈ A, x + y ∈ A) (hAneg : ∀ x ∈ A, -x ∈ A)
    (hX'0 : (0 : J') ∈ X') (hX'add : ∀ x ∈ X', ∀ y ∈ X', x + y ∈ X') (hX'neg : ∀ x ∈ X', -x ∈ X')
    (B : J → J' → L)
    (hBl : ∀ a ∈ A, ∀ a' ∈ A, ∀ y ∈ X', B (a + a') y = B a y * B a' y)
    (hBr : ∀ a ∈ A, ∀ y ∈ X', ∀ y' ∈ X', B a (y + y') = B a y * B a y') :
    Set.ncard {y : J' | y ∈ X' ∧ ∀ a ∈ A, B a y = 1} * Set.ncard A =
      Set.ncard X' * Set.ncard {a : J | a ∈ A ∧ ∀ y ∈ X', B a y = 1} := by sorry
