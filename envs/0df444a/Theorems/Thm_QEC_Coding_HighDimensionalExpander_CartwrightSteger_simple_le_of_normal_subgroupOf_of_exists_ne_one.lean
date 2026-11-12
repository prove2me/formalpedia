-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_simple_le_of_normal_subgroupOf_of_exists_ne_one
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.simple_le_of_normal_subgroupOf_of_exists_ne_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:39:12.815515+00:00
-- url     : https://prove2.me/theorems/6807a745-a980-4686-ac56-bc1c083c8cd6
-- title:
--   Cartwright Steger: simple le of normal subgroup Of of exists ne one
-- statement:
--   A normal subgroup of an ambient finite group which meets a contained
--   simple subgroup nontrivially contains that simple subgroup.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/StrongApproximation.lean#L5495-L5528
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/StrongApproximation.lean#L5495-L5528

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.simple_le_of_normal_subgroupOf_of_exists_ne_one
    {G : Type*} [Group G]
    (S H A : Subgroup G) [IsSimpleGroup S]
    (hSA : S ≤ A)
    [((H.subgroupOf A)).Normal]
    (hne : ∃ g : G, g ∈ H ∧ g ∈ S ∧ g ≠ 1) :
    S ≤ H := by sorry
