-- Prove2me | Theorems.Thm_ValuationSubring_le_trdeg_residueField_comap_of_le_trdeg_residueField
-- name    : ValuationSubring.le_trdeg_residueField_comap_of_le_trdeg_residueField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/61971c0c-aec2-59d8-b75e-7a19d7a7b3cf
-- title:
--   Residue field transcendence degree under restriction of a valuation
-- statement:
--   Let $k \subseteq K \subseteq L$ be fields in one universe, equipped with $k$-algebra structures on $K$ and $L$ and a $K$-algebra structure on $L$ forming a scalar tower. Let $A$ be a valuation subring of $L$ such that $\mathrm{algebraMap}\,k\,L\,(x) \in A$ for every $x \in k$, and let $n_K, n_L$ be natural numbers with $\mathrm{trdeg}_k K = n_K$ and $\mathrm{trdeg}_k L = n_L$ as cardinals. Give the residue field of $A$ the $k$-algebra structure obtained from the corestriction of $\mathrm{algebraMap}\,k\,L$ to $A$ followed by the residue map, and assume $(n_L - 1 : \mathbb{N}) \le \mathrm{trdeg}_k \kappa_A$, the subtraction being truncated subtraction of natural numbers, cast into cardinals. The conclusion concerns $O := A.\mathrm{comap}\,(\mathrm{algebraMap}\,K\,L)$, the valuation subring of $K$ consisting of the elements of $K$ whose image in $L$ lies in $A$; it contains the image of $k$ by the scalar tower identity, and its residue field is made a $k$-algebra in the same way. The assertion is $(n_K - 1 : \mathbb{N}) \le \mathrm{trdeg}_k \kappa_O$.
--
--   This is the transcendence-degree counting step in the construction of valuation subrings of a function field with prescribed residue behaviour, as in Rosenlicht's work on algebraic groups: it transfers a lower bound on the residue transcendence degree of a valuation of $L$ to the valuation of the subfield $K$ obtained by restriction. It is used in [`AlgebraicGeometry.exists_valuationSubring_functionField_of_ringKrullDim_stalk_eq_one`](thm.html#AlgebraicGeometry.exists_valuationSubring_functionField_of_ringKrullDim_stalk_eq_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_le_trdeg_residueField_comap_of_le_trdeg_residueField.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem ValuationSubring.le_trdeg_residueField_comap_of_le_trdeg_residueField
    {k K L : Type u} [Field k] [Field K] [Field L] [Algebra k K] [Algebra K L] [Algebra k L]
    [IsScalarTower k K L]
    (A : ValuationSubring L) (hk : ∀ x : k, algebraMap k L x ∈ A)
    (nK nL : ℕ) (hK : Algebra.trdeg k K = nK) (hL : Algebra.trdeg k L = nL)
    (hA : letI : Algebra k (IsLocalRing.ResidueField A) :=
        ((IsLocalRing.residue A).comp ((algebraMap k L).codRestrict A.toSubring hk)).toAlgebra
      ((nL - 1 : ℕ) : Cardinal) ≤ Algebra.trdeg k (IsLocalRing.ResidueField A)) :
    letI O : ValuationSubring K := A.comap (algebraMap K L)
    letI hkO : ∀ x : k, algebraMap k K x ∈ O := fun x => by
      rw [ValuationSubring.mem_comap, ← IsScalarTower.algebraMap_apply]; exact hk x
    letI : Algebra k (IsLocalRing.ResidueField O) :=
      ((IsLocalRing.residue O).comp ((algebraMap k K).codRestrict O.toSubring hkO)).toAlgebra
    ((nK - 1 : ℕ) : Cardinal) ≤ Algebra.trdeg k (IsLocalRing.ResidueField O) := by sorry
