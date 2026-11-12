-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexCongruencePlace_not_mem_denominatorPlaces_of_projection_eq
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexCongruencePlace_not_mem_denominatorPlaces_of_projection_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:53:13.900534+00:00
-- url     : https://prove2.me/theorems/1b59df65-b2c5-4241-8f68-44171c3277f3
-- title:
--   Cartwright Steger: index Congruence Place not mem denominator Places of projection eq
-- statement:
--   Equality of selected local projections transports selected-place
--   integrality of both an adelic cyclic-algebra unit and its inverse.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadSpecialization.lean#L6294-L6363
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadSpecialization.lean#L6294-L6363

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_IntrinsicStrongApproximation
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Algebra.IsOpenUnits
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped TensorProduct
open scoped commutatorElement
open Topology

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexCongruencePlace_not_mem_denominatorPlaces_of_projection_eq
    (P : BasePrime) (r : Rank) (level : Nat)
    (u v : (ArithmeticFiniteAdeleCyclicAlgebra P r)ˣ)
    (hproj : arithmeticFiniteAdeleCyclicUnitToIndexLocal P r level u =
      arithmeticFiniteAdeleCyclicUnitToIndexLocal P r level v)
    (hv : (v : ArithmeticFiniteAdeleCyclicAlgebra P r) ∈
          ArithmeticFiniteAdeleCyclicIntegralLattice P r ∧
        (↑v⁻¹ : ArithmeticFiniteAdeleCyclicAlgebra P r) ∈
          ArithmeticFiniteAdeleCyclicIntegralLattice P r) :
    indexCongruencePlace P r level ∉
      arithmeticFiniteAdeleCyclicUnitDenominatorPlaces P r u := by sorry
