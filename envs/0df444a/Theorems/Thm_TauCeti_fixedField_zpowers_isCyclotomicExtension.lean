-- Prove2me | Theorems.Thm_TauCeti_fixedField_zpowers_isCyclotomicExtension
-- name    : TauCeti.fixedField_zpowers_isCyclotomicExtension
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:08:52.552708+00:00
-- url     : https://prove2.me/theorems/ebcb8887-5d88-4fd4-96c9-ed98769d3a08
-- title:
--   A cyclotomic extension over the fixed field of a tagged automorphism
-- statement:
--   Let $L/K$ be a finite Galois extension of number fields, let $m\ge1$ be coprime to the absolute discriminant of $L$, and let $M=L(\mu_m)$. Choose a primitive $m$-th root $\zeta\in M$. Under the resulting product identification
--
--   $$
--   \operatorname{Gal}(M/K)\simeq\operatorname{Gal}(L/K)\times(\mathbb Z/m\mathbb Z)^\times,
--   $$
--
--   let $g$ correspond to $(\sigma,\tau)$. If $\operatorname{ord}(\sigma)\mid\operatorname{ord}(\tau)$ and $E=M^{\langle g\rangle}$, then
--
--   $$
--   M=E(\mu_m).
--   $$
--
--   This produces cyclic fixed fields over which the ambient compositum remains cyclotomic.
--
--   Source: the [Tau Ceti contributors](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/Chebotarev/TaggedFixedField.lean#L50-L72) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`).
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/Chebotarev/TaggedFixedField.lean

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_FieldTheory_IntermediateField_Adjoin_EqTop
import Definitions.Def_TauCeti_NumberTheory_NumberField_Cyclotomic_Compositum
import Definitions.Def_TauCeti_NumberTheory_NumberField_Cyclotomic_Finrank
import Definitions.Def_TauCeti_RingTheory_RootsOfUnity_PrimitiveRoots
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.FieldTheory.Normal.Defs
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# The tagged fixed fields are cyclotomic

`M / K` is Galois with `Gal(M/K)` split by `galEquivProd` as `Gal(L/K) × (ZMod m)ˣ`, the second
factor being the cyclotomic character on the `m`-th roots of unity. A *tag* is a pair `(σ, τ)` in
that product. This file shows that when the tag satisfies `orderOf σ ∣ orderOf τ`, the field fixed
by the cyclic subgroup the tag generates has `M` as an `m`-th cyclotomic extension.

## Main results

* `TauCeti.fixedField_zpowers_isCyclotomicExtension`: for a tag `(σ, τ)` with
  `orderOf σ ∣ orderOf τ`, `M / fixedField ⟪(σ, τ)⟫` is an `m`-th cyclotomic extension.
* `TauCeti.card_algEquiv_fixedField_zpowers_eq_orderOf`: `M` has `orderOf τ` automorphisms over
  that fixed field.

## References

The result is due to the Birkbeck--Brasca Chebotarev development,
[CBirkbeck/chebotarev-density](https://github.com/CBirkbeck/chebotarev-density) (Apache-2.0), at
commit `55a89985d47a3befcf6069aca1da250ff088b5c7`. There it is two private declarations in
`CebotarevDensity/Abelian.lean`: `compositum_isCyclotomic_over_fixedField`, which assumes the meet
is trivial, and `zpowers_inf_fixingSubgroup_eq_bot_aux`, which supplies that hypothesis. The source
combines them at their call site rather than stating a single theorem. The hypothesis taken here is
`orderOf σ ∣ orderOf τ`, where the source asks for `Nat.card Gal(L/K) ∣ orderOf τ`.
-/

 section

open _root_.IntermediateField _root_.IsCyclotomicExtension
open scoped _root_.NumberField

namespace TauCeti
end TauCeti
section TauCeti
open TauCeti

variable (K L M : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Field M]
  [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M] [IsGalois K L]
  (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} L M]

theorem TauCeti.fixedField_zpowers_isCyclotomicExtension
    (hcop : ((_root_.NumberField.discr L).natAbs).Coprime m) {ζ : M} (hζ : _root_.IsPrimitiveRoot ζ m)
    (σ : Gal(L/K)) (τ : (_root_.ZMod m)ˣ) (hστ : _root_.orderOf σ ∣ _root_.orderOf τ) :
    _root_.IsCyclotomicExtension {m}
      (_root_.IntermediateField.fixedField (_root_.Subgroup.zpowers ((_root_.IsCyclotomicExtension.galEquivProd K L M m hcop hζ).symm (σ, τ)))) M := by sorry
