-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_isOpen_arithmeticFiniteAdelesIntegralAtIndex
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.isOpen_arithmeticFiniteAdelesIntegralAtIndex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:12:22.903956+00:00
-- url     : https://prove2.me/theorems/102e65a1-56ca-4dd9-8085-881e70c8d334
-- title:
--   Cartwright Steger: is Open arithmetic Finite Adeles Integral At Index
-- statement:
--   Integrality at the selected congruence coordinate is an open condition
--   in the genuine arithmetic finite-adele ring.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadSpecialization.lean#L4664-L4670
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/PrasadSpecialization.lean#L4664-L4670

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
open scoped PowerSeries.WithPiTopology Topology WithZeroTopology Multiplicative
open MonoidWithZeroHom.ValueGroup₀
open Filter
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.selectedPlaceResidueFieldTopologicalSpace
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.selectedPlaceResidueFieldDiscreteTopology

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.isOpen_arithmeticFiniteAdelesIntegralAtIndex
    (P : BasePrime) (r : Rank) (level : Nat) :
    IsOpen (ArithmeticFiniteAdelesIntegralAtIndex P r level :
      Set (ArithmeticFiniteAdeleRing P)) := by sorry
