-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_map_orderNormOneCongruenceSubgroup_equivFullNormOne
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.map_orderNormOneCongruenceSubgroup_equivFullNormOne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:18:21.154437+00:00
-- url     : https://prove2.me/theorems/1bc8fff4-e33a-47ef-871e-67558057ab08
-- title:
--   Cartwright Steger: map order Norm One Congruence Subgroup equiv Full Norm One
-- statement:
--   The special-linear and full-kernel presentations define exactly the same
--   genuine norm-one congruence subgroup `H₁`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/StrongApproximation.lean#L5153-L5189
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/StrongApproximation.lean#L5153-L5189

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.map_orderNormOneCongruenceSubgroup_equivFullNormOne
    (P : BasePrime) (r : Rank) (level : Nat) :
    (OrderNormOneCongruenceSubgroup P r level).map
        (orderNormOneInnerFormEquivFullNormOne P r).toMonoidHom =
      OrderInnerFormNormOneCongruenceSubgroup P r level := by sorry
