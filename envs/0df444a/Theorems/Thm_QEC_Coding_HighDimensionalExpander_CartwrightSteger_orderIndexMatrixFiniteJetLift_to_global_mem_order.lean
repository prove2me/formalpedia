-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_orderIndexMatrixFiniteJetLift_to_global_mem_order
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderIndexMatrixFiniteJetLift_to_global_mem_order
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:37:41.863028+00:00
-- url     : https://prove2.me/theorems/9d8cde06-5300-4e1a-8a8a-936dac682bd7
-- title:
--   Cartwright Steger: order Index Matrix Finite Jet Lift to global mem order
-- statement:
--   The Cartwright Steger construction uses the order Index Matrix Finite Jet Lift to global mem order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/StrongApproximation.lean#L2706-L2741
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/StrongApproximation.lean#L2706-L2741

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.orderIndexMatrixFiniteJetLift_to_global_mem_order
    (P : BasePrime) (r : Rank) (level : Nat)
    (M : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (PowerSeries (ResidueField P r level)))
    (n : Nat) :
    (orderIndexMatrixFiniteJetLift P r level M n).map
        (constantArithmeticToSplittingFunctionField P r) ∈
      CartwrightStegerOrder P r := by sorry
