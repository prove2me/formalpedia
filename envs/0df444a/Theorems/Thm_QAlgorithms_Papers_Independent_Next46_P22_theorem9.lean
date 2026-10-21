-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P22_theorem9
-- name    : QAlgorithms.Papers.Independent.Next46.P22.theorem9
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T13:52:15.856187+00:00
-- url     : https://prove2.me/theorems/5e1c39b1-36b2-4d31-b7fa-e7a2ff3ce4b5
-- title:
--   Theorem 9
-- statement:
--   Let $F$ have characteristic zero, $G$ be any group, $L=\bigoplus_gL^{(g)}$ a graded Lie algebra, and $V=\bigoplus_gV^{(g)}$ a finite-dimensional graded $L$-module. The compatibility is $L^{(g)}V^{(h)}\subseteq V^{(gh)}$. If the underlying ordinary $L$-module is completely reducible, there are irreducible graded $L$-submodules $V_i$ with
--
--   $$V=V_1\oplus\cdots\oplus V_s.$$
--
--   There is no dimension or semisimplicity restriction on $L$, and no finiteness or commutativity restriction on $G$. The sum is internal and finite; the index set may be empty when $V=0$. Irreducibility means that every $L$-invariant subspace of a summand that also preserves the additional structure is zero or the whole summand.
-- source:
--   Structure of H-(co)module Lie algebras, arXiv:1205.0778v7, PDF p. 13, Theorem 9

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P22

namespace QAlgorithms.Papers.Independent.Next46.P22

noncomputable section

open scoped TensorProduct

open Classical

section Statements

variable {F H L : Type*} [Field F] [Ring H] [HopfAlgebra F H] [LieRing L] [LieAlgebra F L]

variable {V W : Type*} [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]

section LieModules

variable [LieRingModule L V] [LieModule F L V] [LieRingModule L W] [LieModule F L W]

/-- Theorem 9, PDF p.13: arbitrary grading group and no dimension condition on L. -/
theorem theorem9 [CharZero F] [FiniteDimensional F V]
    {G : Type*} [Group G] (D : Grading F G L) (hD : GradedLie D)
    (E : Grading F G V) (hE : GradedCompatible D E)
    (hcr : CompletelyReducible F L V) :
    IrreducibleDecomposition (L := L) (GradedSubspace E) := by sorry

end LieModules

end Statements

end

end QAlgorithms.Papers.Independent.Next46.P22
