-- Prove2me | Theorems.Thm_TauCeti_GlobalNumberFields_ker_residueSignRayClass
-- name    : TauCeti.GlobalNumberFields.ker_residueSignRayClass
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T20:44:31.727293+00:00
-- url     : https://prove2.me/theorems/8d5f54e6-cf38-40c6-96ba-a3659c2cbfdd
-- title:
--   Exactness of the residue-and-sign map into the ray class group
-- statement:
--   Let $K$ be a number field and $\mathfrak m=(\mathfrak m_0,\mathfrak m_\infty)$ a modulus, with nonzero integral ideal $\mathfrak m_0$ and a finite set $\mathfrak m_\infty$ of real places. Put
--
--   $$
--   R_{\mathfrak m}=(\mathcal O_K/\mathfrak m_0)^\times\times\{\pm1\}^{\mathfrak m_\infty}.
--   $$
--
--   Let $u:\mathcal O_K^\times\to R_{\mathfrak m}$ record the residue and signs of a unit, and let $r:R_{\mathfrak m}\to\operatorname{Cl}_{\mathfrak m}(K)$ attach the principal ray class of an element with those residues and signs. Then
--
--   $$
--   \ker r=\operatorname{im}u.
--   $$
--
--   This is exactness at the residue-and-sign term in the ray class exact sequence.
--
--   Source: the [Tau Ceti contributors](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/Global/RayClass/Exact.lean#L269-L285) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`).
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/Global/RayClass/Exact.lean#L269-L285

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_Algebra_Order_Ring_Units
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_Approximation_Weak
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Basic
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_CongruenceQuotient
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Exact
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Modulus
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Residue
import Definitions.Def_TauCeti_NumberTheory_NumberField_Ideal_Away
import Definitions.Def_TauCeti_NumberTheory_NumberField_SignApproximation
import Definitions.Def_TauCeti_NumberTheory_NumberField_Units_Signature_Basic
import Definitions.Def_TauCeti_NumberTheory_NumberField_Units_Signature_Integer
import Definitions.Def_TauCeti_RingTheory_DedekindDomain_Factorization
import Definitions.Def_TauCeti_RingTheory_DedekindDomain_Ideal
import Definitions.Def_TauCeti_RingTheory_Ideal_Quotient_Representative
import Definitions.Def_TauCeti_RingTheory_Valuation_AbsoluteValue
import Definitions.Def_TauCeti_RingTheory_Valuation_Approximation
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.Algebra.Order.Ring.Units
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.Data.Int.WithZero
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.Tactic.Group

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# The ray class exact sequence

For a modulus `m` of a number field `K`, forgetting its congruence and sign conditions sends a ray
class to an ordinary ideal class.  This file constructs the full exact sequence

```text
1 → unitsCongruenceSubgroup m → (𝓞 K)ˣ → A m → RayClassGroup m → ClassGroup (𝓞 K) → 1,
```

where `A m = (𝓞 K ⧸ m.finitePart)ˣ × (m.infinitePart → ℤˣ)` records residues and prescribed
signs.  It also retains the useful coarser exact tail
`primeToSubgroup m → RayClassGroup m → ClassGroup (𝓞 K) → 1`.

In the coarser tail, the first map sends an element of `Kˣ` that is a unit at the finite part to
the ray class of its principal ideal.  The second map is surjective, and its kernel is exactly the
range of the first.  Surjectivity of the transition maps follows by weak approximation, and
surjectivity onto the ordinary class group follows by transition to the trivial modulus.

The kernel of `A m → RayClassGroup m` is the image of the integer units, while the kernel of the
map from integer units to `A m` is `unitsCongruenceSubgroup m`.  The resulting exact sequence is
the input to the ray class number formula.

## Main definitions

* `TauCeti.GlobalNumberFields.principalRayClass`: the ray class of a principal fractional ideal
  whose generator is a unit at the finite part.
* `TauCeti.GlobalNumberFields.rayClassToClassGroup`: the ordinary ideal class underlying a ray
  class.
* `TauCeti.GlobalNumberFields.unitsResidueSignHom`: the residues and signs of the integer units.
* `TauCeti.GlobalNumberFields.residueSignRayClass`: the principal ray class of a residue unit and
  sign pattern.

## Main results

* `TauCeti.GlobalNumberFields.rayClassToClassGroup_surjective`: every ordinary ideal class lifts
  to a ray class.
* `TauCeti.GlobalNumberFields.ker_rayClassToClassGroup`: the kernel consists exactly of ray
  classes of principal ideals generated by elements in `primeToSubgroup m`.
* `TauCeti.GlobalNumberFields.mulExact_principalRayClass_rayClassToClassGroup`: the corresponding
  multiplicative exactness statement.
* `TauCeti.GlobalNumberFields.classMap_surjective`: every transition between ray class groups is
  surjective.
* `TauCeti.GlobalNumberFields.ker_unitsResidueSignHom`,
  `TauCeti.GlobalNumberFields.ker_residueSignRayClass` and
  `TauCeti.GlobalNumberFields.range_residueSignRayClass`: the three nontrivial exactness statements
  in the full sequence.
* `TauCeti.GlobalNumberFields.mulExact_unitsCongruenceSubgroup_unitsResidueSignHom`,
  `TauCeti.GlobalNumberFields.mulExact_unitsResidueSignHom_residueSignRayClass` and
  `TauCeti.GlobalNumberFields.mulExact_residueSignRayClass_rayClassToClassGroup`: their
  multiplicative exactness forms.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
* S. Lang, *Algebraic Number Theory*, Chapter VI, §1.
-/

 section

open IsDedekindDomain NumberField
open scoped nonZeroDivisors NumberField

namespace TauCeti.GlobalNumberFields
end TauCeti.GlobalNumberFields
section TauCeti.GlobalNumberFields
open TauCeti TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]





















/-! ### The residue-and-sign presentation of the exact sequence -/

theorem TauCeti.GlobalNumberFields.ker_residueSignRayClass (𝔪 : _root_.TauCeti.GlobalNumberFields.Modulus K) :
    (_root_.TauCeti.GlobalNumberFields.residueSignRayClass 𝔪).ker = (_root_.TauCeti.GlobalNumberFields.unitsResidueSignHom 𝔪).range := by sorry
