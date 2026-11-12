-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_ne_one_mem_IndexNormOneCartwrightStegerLiftImage
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_ne_one_mem_IndexNormOneCartwrightStegerLiftImage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:50:24.472267+00:00
-- url     : https://prove2.me/theorems/88881315-00b3-4a5b-b815-80f08b4e106e
-- title:
--   Cartwright Steger: exists ne one mem Index Norm One Cartwright Steger Lift Image
-- statement:
--   The finite image of the norm-one lift lattice is nontrivial, witnessed by
--   the ratio of two distinct explicit Cartwright--Steger generators.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/StrongApproximation.lean#L5279-L5303
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/StrongApproximation.lean#L5279-L5303

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_ne_one_mem_IndexNormOneCartwrightStegerLiftImage
    (P : BasePrime) (r : Rank) (level : Nat) :
    ∃ g : PSL P r level,
      g ∈ IndexNormOneCartwrightStegerLiftImage P r level ∧ g ≠ 1 := by sorry
