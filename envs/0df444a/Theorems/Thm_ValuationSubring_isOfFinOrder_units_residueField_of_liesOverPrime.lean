-- Prove2me | Theorems.Thm_ValuationSubring_isOfFinOrder_units_residueField_of_liesOverPrime
-- name    : ValuationSubring.isOfFinOrder_units_residueField_of_liesOverPrime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/26c8d27a-72ab-5663-87c2-e8f6ecf7ffa5
-- title:
--   Units in residue fields of places of ℚ̄ are torsion
-- statement:
--   Let $p$ be a natural number that is prime, let $A$ be a valuation subring of the algebraic closure $\overline{\mathbb Q}$ of $\mathbb Q$ (as constructed by `AlgebraicClosure`), and assume `A.LiesOverPrime p`, which by definition says that the image of $p$ in $\overline{\mathbb Q}$ belongs to `A.nonunits`, the set of elements of the ambient field whose valuation under the valuation attached to $A$ is $<1$; equivalently, $p$ lies in the maximal ideal of $A$. Let $u$ be a unit of the residue field `IsLocalRing.ResidueField ↥A` of the local ring $A$. Then $u$ satisfies `IsOfFinOrder`, i.e. there is an $n \ge 1$ with $u^{n} = 1$. Since the residue field is a field, this asserts exactly that every nonzero element of the residue field of such a valuation subring is a root of unity.
--
--   This is the standard fact that the residue field at a place of $\overline{\mathbb Q}$ above $p$ is an algebraic extension of $\mathbb F_p$, hence a union of finite fields, so that its multiplicative group is torsion. It is used on the modular-curve side of the development, where points of special fibres over such residue fields must be torsion: it is cited in [`ModularCurve.DRModelPackage.exists_schemeNsmul_eq_one_residueField_point`](thm.html#ModularCurve.DRModelPackage.exists_schemeNsmul_eq_one_residueField_point) and in the computations of the degree and genus of the function field of $X_1$ over an algebraically closed base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_isOfFinOrder_units_residueField_of_liesOverPrime.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ValuationSubring.isOfFinOrder_units_residueField_of_liesOverPrime (p : ℕ) [Fact p.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (u : (IsLocalRing.ResidueField ↥A)ˣ) : IsOfFinOrder u := by sorry
