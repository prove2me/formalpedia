-- Prove2me | Theorems.Thm_TypeDensity_form_product_maps_to_and_preserves
-- name    : TypeDensity.form_product_maps_to_and_preserves
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T13:31:06.857122+00:00
-- url     : https://prove2.me/theorems/4d87c40a-07cc-4dc1-8cca-6d5de0d5ed7b
-- title:
--   The normalized product of factor cells lands in the product cell, has the expected reduction and unit `μ`-coordinate, and preserves congruences modulo `m^L`.
-- statement:
--   The normalized product of factor cells lands in the product cell, has the expected reduction and unit `μ`-coordinate, and preserves congruences modulo `m^L`.
-- source:
--   TypeDensity/Unramified/Extension.lean#L687-L768

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
set_option autoImplicit false

open TypeDensity
open Polynomial IsLocalRing MeasureTheory

theorem TypeDensity.form_product_maps_to_and_preserves (O : Type) [CommRing O] [IsLocalRing O] (ι : Type)
    [Fintype ι] (d : ι → ℕ) (ν : ∀ i, Fin (d i + 1))
    (g : ∀ i, Fin (d i + 1) → IsLocalRing.ResidueField O)
    (μ : Fin ((∑ i, d i) + 1)) (hμ : formProd d g μ = 1)
    (a a' : ∀ i, Fin (d i) → O)
    (ha : a ∈ Set.pi Set.univ (fun i => reducedFormCell O (d i) (ν i) (g i)))
    (ha' : a' ∈ Set.pi Set.univ (fun i => reducedFormCell O (d i) (ν i) (g i))) :
    reducedFormProduct O d ν g μ a ∈ reducedFormCell O (∑ i, d i) μ (formProd d g) ∧
      residueVector O (formProd d (fun i => insertOne (ν i) (a i))) = formProd d g ∧ IsUnit
      (formProd d (fun i => insertOne (ν i) (a i)) μ) ∧ ∀ L : ℕ,
      (∀ i j, a i j - a' i j ∈ (IsLocalRing.maximalIdeal O) ^ L) → ∀ j,
      reducedFormProduct O d ν g μ a j - reducedFormProduct O d ν g μ a' j ∈
      (IsLocalRing.maximalIdeal O) ^ L := by sorry
