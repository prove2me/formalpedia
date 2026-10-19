-- Prove2me | Theorems.Thm_TypeDensity_residue_cell_cylinder
-- name    : TypeDensity.residue_cell_cylinder
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:00:36.547888+00:00
-- url     : https://prove2.me/theorems/a8526f72-72cd-43a8-897c-f9d5b9991857
-- title:
--   A residue cell is a congruence class modulo `m` around any of its points;
-- statement:
--   A residue cell is a congruence class modulo `m` around any of its points; it is nonempty iff `G` is monic of degree `n`.
-- source:
--   TypeDensity/Unramified/PolynomialTypes.lean#L794-L835

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Formula_LawAlgebra
import Definitions.Def_TypeDensity_Algebra_AlgebraType
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Definitions.Def_TypeDensity_Measure_PrimitiveLocus
import Definitions.Def_TypeDensity_Algebra_FactorInvariant
import Theorems.Thm_TypeDensity_monic_poly_reconstruct
import Theorems.Thm_TypeDensity_polynomial_congruence_and_product
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Henselian
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.NumberTheory.Padics.RingHoms
set_option autoImplicit false

open TypeDensity
open scoped ENNReal

theorem TypeDensity.residue_cell_cylinder (O : Type) [CommRing O] [IsLocalRing O] (n : ℕ)
    (G : Polynomial (IsLocalRing.ResidueField O)) :
    (∀ a ∈ residueCell O n G, residueCell O n G =
        {b | ∀ i, b i - a i ∈ IsLocalRing.maximalIdeal O}) ∧
      (G.Monic → G.natDegree = n → (residueCell O n G).Nonempty) ∧
      ((residueCell O n G).Nonempty → G.Monic ∧ G.natDegree = n) := by sorry
