-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingNormOneLocal_not_compactSpace
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingNormOneLocal_not_compactSpace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:45:54.271714+00:00
-- url     : https://prove2.me/theorems/2e57d560-743f-41f1-8b33-d9d9b4ca4e42
-- title:
--   Cartwright Steger: building Norm One Local not compact Space
-- statement:
--   The split norm-one factor at the distinguished building place is not
--   compact.  This discharges the noncompact-place premise in the LSV strong
--   approximation argument with the concrete local representation: a compact
--   group would have bounded second-coordinate image, whereas the explicit
--   norm-one apartment ray has second coordinate `π⁻ⁿ`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/StrongApproximation.lean#L159-L201
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/StrongApproximation.lean#L159-L201

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingNormOneLocal_not_compactSpace
    (P : BasePrime) (r : Rank) :
    ¬ CompactSpace
      (Matrix.SpecialLinearGroup (Fin r.matrixRank) (BuildingLocalField P)) := by sorry
