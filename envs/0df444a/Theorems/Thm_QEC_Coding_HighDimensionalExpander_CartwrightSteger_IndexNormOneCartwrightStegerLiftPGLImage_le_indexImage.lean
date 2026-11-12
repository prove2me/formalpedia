-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_IndexNormOneCartwrightStegerLiftPGLImage_le_indexImage
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.IndexNormOneCartwrightStegerLiftPGLImage_le_indexImage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:20:13.366561+00:00
-- url     : https://prove2.me/theorems/c50d3615-c873-41eb-b1bb-53bc79144b34
-- title:
--   Cartwright Steger: Index Norm One Cartwright Steger Lift PGLImage le index Image
-- statement:
--   Every finite point produced by the norm-one lift lattice belongs to the
--   actual Cartwright--Steger finite image.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/StrongApproximation.lean#L5354-L5363
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/StrongApproximation.lean#L5354-L5363

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.IndexNormOneCartwrightStegerLiftPGLImage_le_indexImage
    (P : BasePrime) (r : Rank) (level : Nat) :
    IndexNormOneCartwrightStegerLiftPGLImage P r level ≤
      IndexCartwrightStegerImage P r level := by sorry
