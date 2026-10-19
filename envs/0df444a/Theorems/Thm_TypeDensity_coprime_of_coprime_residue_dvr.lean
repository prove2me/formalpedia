-- Prove2me | Theorems.Thm_TypeDensity_coprime_of_coprime_residue_dvr
-- name    : TypeDensity.coprime_of_coprime_residue_dvr
-- status  : Proved
-- author  : @asving
-- created : 2026-10-16T14:00:35.593066+00:00
-- url     : https://prove2.me/theorems/d63662e9-9bbe-428f-86a7-00b4f9d59893
-- title:
--   Monic polynomials over a local ring `R` with coprime reductions stay coprime over any `R`-algebra `K` (classically: the fraction field of a DVR).
-- statement:
--   Monic polynomials over a local ring `R` with coprime reductions stay coprime over any `R`-algebra `K` (classically: the fraction field of a DVR).
-- source:
--   TypeDensity/Unramified/Extension.lean#L437-L443

import Definitions.Def_TypeDensity_Basic
import Definitions.Def_TypeDensity_Measure_AdicCylinders
import Definitions.Def_TypeDensity_Measure_HenselProducts
import Definitions.Def_TypeDensity_Unramified_Extension
import Theorems.Thm_TypeDensity_isCoprime_of_isCoprime_map_residue
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

theorem TypeDensity.coprime_of_coprime_residue_dvr (R K : Type) [CommRing R] [IsLocalRing R] [CommRing K]
    [Algebra R K] (A B : Polynomial R) (hA : A.Monic) (hB : B.Monic)
    (hc : IsCoprime (A.map (IsLocalRing.residue R)) (B.map (IsLocalRing.residue R))) :
    IsCoprime (A.map (algebraMap R K)) (B.map (algebraMap R K)) := by sorry
