-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cartwrightStegerOrderProjectivization_eq_of_globalPGL_eq
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerOrderProjectivization_eq_of_globalPGL_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:48:52.202691+00:00
-- url     : https://prove2.me/theorems/0d67e30e-0211-4743-83dd-514d0afae5d6
-- title:
--   Cartwright Steger: cartwright Steger Order Projectivization eq of global PGL eq
-- statement:
--   Equality of global projective matrices detects equality in the genuine
--   projective unit group of the arithmetic order.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/StrongApproximation.lean#L4620-L4643
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/StrongApproximation.lean#L4620-L4643

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_SimpleTransitivity
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_SpecialLinear
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Reduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicDivisionAlgebra
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.Algebra.Central.Matrix
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_StrongApproximation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups SphericalHecke.LocalTopology Valued

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.cartwrightStegerOrderProjectivization_eq_of_globalPGL_eq
    (P : BasePrime) (r : Rank)
    (u v : (CartwrightStegerOrder P r)ˣ)
    (hglobal : orderUnitToGlobalPGL P r u =
      orderUnitToGlobalPGL P r v) :
    cartwrightStegerOrderProjectivization P r u =
      cartwrightStegerOrderProjectivization P r v := by sorry
