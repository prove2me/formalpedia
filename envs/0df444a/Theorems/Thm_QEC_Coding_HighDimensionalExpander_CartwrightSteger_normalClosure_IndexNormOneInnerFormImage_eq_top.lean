-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_normalClosure_IndexNormOneInnerFormImage_eq_top
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.normalClosure_IndexNormOneInnerFormImage_eq_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:16:02.337274+00:00
-- url     : https://prove2.me/theorems/cd0c2c9b-d907-444b-9556-23536f967495
-- title:
--   Cartwright Steger: normal Closure Index Norm One Inner Form Image eq top
-- statement:
--   Simplicity and the explicit generator ratio already imply that the
--   normal closure of the genuine norm-one reduction image is all of finite
--   `PSL`.  Thus the remaining strong-approximation content is precisely
--   conjugation stability of this actual image, not nontriviality or simplicity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/StrongApproximation.lean#L4014-L4030
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/StrongApproximation.lean#L4014-L4030

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.normalClosure_IndexNormOneInnerFormImage_eq_top
    (P : BasePrime) (r : Rank) (level : Nat) :
    Subgroup.normalClosure
        (IndexNormOneInnerFormImage P r level : Set (PSL P r level)) = ⊤ := by sorry
