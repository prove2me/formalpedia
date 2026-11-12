-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_normalClosure_IndexNormOneGeneratorRatioSubgroup_eq_top
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.normalClosure_IndexNormOneGeneratorRatioSubgroup_eq_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:15:27.256816+00:00
-- url     : https://prove2.me/theorems/d944d073-18b7-40e4-bd6f-ba67bdb58e46
-- title:
--   Cartwright Steger: normal Closure Index Norm One Generator Ratio Subgroup eq top
-- statement:
--   The normal closure of the explicit global norm-one generator ratios is
--   the whole finite `PSL`.  Hence the remaining construction-specific global
--   step is conjugation stability of this concrete subgroup, not generation of
--   new nonidentity witnesses or another simplicity argument.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/StrongApproximation.lean#L3990-L4008
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/StrongApproximation.lean#L3990-L4008

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.normalClosure_IndexNormOneGeneratorRatioSubgroup_eq_top
    (P : BasePrime) (r : Rank) (level : Nat) :
    Subgroup.normalClosure
        (IndexNormOneGeneratorRatioSubgroup P r level :
          Set (PSL P r level)) = ⊤ := by sorry
