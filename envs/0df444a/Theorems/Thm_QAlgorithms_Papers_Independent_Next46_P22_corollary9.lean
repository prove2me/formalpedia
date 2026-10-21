-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P22_corollary9
-- name    : QAlgorithms.Papers.Independent.Next46.P22.corollary9
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T13:51:13.716119+00:00
-- url     : https://prove2.me/theorems/b7231d1e-5810-4364-8313-e988ed0ca6f5
-- title:
--   Corollary to Theorem 9
-- statement:
--   Let $F$ have characteristic zero, $G$ be any group and $L$ a finite-dimensional semisimple $G$-graded Lie algebra. If $V$ is any finite-dimensional graded $L$-module, with $L^{(g)}V^{(h)}\subseteq V^{(gh)}$, then
--
--   $$V=V_1\oplus\cdots\oplus V_s$$
--
--   for irreducible graded $L$-submodules $V_i$. Ordinary complete reducibility is not assumed; the group can be infinite and nonabelian. The sum is internal and finite; the index set may be empty when $V=0$. Irreducibility means that every $L$-invariant subspace of a summand that also preserves the additional structure is zero or the whole summand.
-- source:
--   Structure of H-(co)module Lie algebras, arXiv:1205.0778v7, PDF p. 13, Corollary to Theorem 9

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

/-- Corollary to Theorem 9, PDF p.13: Weyl version, no ordinary reducibility assumption. -/
theorem corollary9 [CharZero F] [FiniteDimensional F L] [FiniteDimensional F V]
    (hL : Semisimple F L) {G : Type*} [Group G]
    (D : Grading F G L) (hD : GradedLie D)
    (E : Grading F G V) (hE : GradedCompatible D E) :
    IrreducibleDecomposition (L := L) (GradedSubspace E) := by sorry

end LieModules

end Statements

end

end QAlgorithms.Papers.Independent.Next46.P22
