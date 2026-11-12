-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_mem_CartwrightStegerNormOneLiftLattice_iff
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.mem_CartwrightStegerNormOneLiftLattice_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:09:15.469234+00:00
-- url     : https://prove2.me/theorems/7fca84cc-765f-4e19-b1ac-31a6bbaa1271
-- title:
--   Cartwright Steger: mem Cartwright Steger Norm One Lift Lattice iff
-- statement:
--   The Cartwright Steger construction uses the mem Cartwright Steger Norm One Lift Lattice iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/StrongApproximation.lean#L787-L793
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/StrongApproximation.lean#L787-L793

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.mem_CartwrightStegerNormOneLiftLattice_iff
    (P : BasePrime) (r : Rank)
    (u : (CartwrightStegerOrder P r)ˣ) :
    u ∈ CartwrightStegerNormOneLiftLattice P r ↔
      u ∈ CartwrightStegerOrderUnitLattice P r ∧
        Matrix.GeneralLinearGroup.det (orderUnitToGlobalGL P r u) = 1 := by sorry
