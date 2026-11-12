-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingCyclicScalarExtensionNormOne_not_compactSpace
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingCyclicScalarExtensionNormOne_not_compactSpace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:08:37.609905+00:00
-- url     : https://prove2.me/theorems/f653f745-092b-4341-8cec-2f06fe15ab3d
-- title:
--   Cartwright Steger: building Cyclic Scalar Extension Norm One not compact Space
-- statement:
--   The actual local norm-one group of the Cartwright--Steger cyclic algebra
--   is noncompact at the building place.  This is the exact structural premise
--   used by strong approximation, now stated on the genuine scalar extension.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/StrongApproximation.lean#L660-L668
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/StrongApproximation.lean#L660-L668

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingCyclicScalarExtensionNormOne_not_compactSpace
    (P : BasePrime) (r : Rank) :
    ¬ CompactSpace (BuildingCyclicScalarExtensionNormOne P r) := by sorry
