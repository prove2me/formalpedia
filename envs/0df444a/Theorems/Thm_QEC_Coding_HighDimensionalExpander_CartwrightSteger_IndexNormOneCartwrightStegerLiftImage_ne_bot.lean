-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_IndexNormOneCartwrightStegerLiftImage_ne_bot
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.IndexNormOneCartwrightStegerLiftImage_ne_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:19:16.152194+00:00
-- url     : https://prove2.me/theorems/31469491-4b3f-47da-be29-6f69dc548503
-- title:
--   Cartwright Steger: Index Norm One Cartwright Steger Lift Image ne bot
-- statement:
--   The Cartwright Steger construction uses the Index Norm One Cartwright Steger Lift Image ne bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/StrongApproximation.lean#L5305-L5312
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/StrongApproximation.lean#L5305-L5312

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.IndexNormOneCartwrightStegerLiftImage_ne_bot
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexNormOneCartwrightStegerLiftImage P r level ≠ ⊥ := by sorry
