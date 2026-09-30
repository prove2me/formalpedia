-- Prove2me | Theorems.Thm_TauCeti_GlobalNumberFields_rayClassCharacterPartialSum_eq_sum
-- name    : TauCeti.GlobalNumberFields.rayClassCharacterPartialSum_eq_sum
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T20:45:02.584379+00:00
-- url     : https://prove2.me/theorems/592c7725-6015-4176-940d-cc17dea49ce5
-- title:
--   Decomposition of a ray class character sum by ideal classes
-- statement:
--   Let $K$ be a number field and $\mathfrak m=(\mathfrak m_0,\mathfrak m_\infty)$ a modulus, with nonzero integral ideal $\mathfrak m_0$ and a finite set $\mathfrak m_\infty$ of real places. Let $\chi:\operatorname{Cl}_{\mathfrak m}(K)\to\mathbb C^\times$ be a ray class character and let $x\in\mathbb R$. For each ray class $c$, write $A_c(x)$ for the number of nonzero integral ideals prime to $\mathfrak m_0$, of norm at most $x$, whose ray class is $c$. Then
--
--   $$
--   \sum_{\substack{0\ne I\subseteq\mathcal O_K\\(I,\mathfrak m_0)=1\\NI\le x}}\chi([I]_{\mathfrak m})
--   =\sum_{c\in\operatorname{Cl}_{\mathfrak m}(K)}\chi(c)A_c(x).
--   $$
--
--   This expresses a character sum as a finite weighted combination of individual ray class counts.
--
--   Source: the [Tau Ceti contributors](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/Global/RayClass/Character/Sum.lean#L62-L80) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`).
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/NumberField/Global/RayClass/Character/Sum.lean#L62-L80

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Basic
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Character_Basic
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Character_Sum
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Count_Basic
import Definitions.Def_TauCeti_NumberTheory_NumberField_Global_RayClass_Modulus
import Definitions.Def_TauCeti_NumberTheory_NumberField_Ideal_Away
import Definitions.Def_TauCeti_Order_Northcott_Basic
import Definitions.Def_TauCeti_RingTheory_DedekindDomain_Factorization
import Definitions.Def_TauCeti_RingTheory_DedekindDomain_Ideal
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.Algebra.Order.Ring.Units
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.Data.Int.WithZero
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Set.Card
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
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Northcott
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.Tactic.Group
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.UniformSpace.Real

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Character sums over the integral ideals of bounded norm

Let `𝔪` be a modulus of a number field `K` and `χ` a ray class character of `𝔪`.  This file
introduces `rayClassCharacterPartialSum 𝔪 χ x`, the sum of `χ` over the nonzero integral ideals
prime to the finite part of `𝔪` whose norm is at most `x`, and identifies it with the
`χ`-weighted combination of the ray class counting functions.

The sum ranges over ideals, not over chosen class representatives.  Regrouping it by ray class is
exactly the partition `idealClassSigmaEquiv`, and on each fibre `χ` is constant, so each class
contributes its counting function scaled by the single value `χ` takes there.

## Main definitions

* `TauCeti.GlobalNumberFields.rayClassCharacterPartialSum`: the partial sum of a ray class
  character over the integral ideals of bounded norm.

## Main results

* `TauCeti.GlobalNumberFields.rayClassCharacterPartialSum_eq_sum`: the partial sum is
  `∑ c, χ c * rayClassIdealCountingFunction 𝔪 c x`.
-/

 section

namespace TauCeti.GlobalNumberFields
end TauCeti.GlobalNumberFields
section TauCeti.GlobalNumberFields
open TauCeti TauCeti.GlobalNumberFields

open scoped _root_.NumberField

variable {K : Type*} [Field K] [NumberField K]

theorem TauCeti.GlobalNumberFields.rayClassCharacterPartialSum_eq_sum (𝔪 : _root_.TauCeti.GlobalNumberFields.Modulus K) [_root_.Fintype (_root_.TauCeti.GlobalNumberFields.RayClassGroup 𝔪)]
    (χ : _root_.TauCeti.GlobalNumberFields.RayClassCharacter 𝔪) (x : ℝ) :
    _root_.TauCeti.GlobalNumberFields.rayClassCharacterPartialSum 𝔪 χ x =
      ∑ c : _root_.TauCeti.GlobalNumberFields.RayClassGroup 𝔪, (χ c : ℂ) * _root_.TauCeti.GlobalNumberFields.rayClassIdealCountingFunction 𝔪 c x := by sorry
