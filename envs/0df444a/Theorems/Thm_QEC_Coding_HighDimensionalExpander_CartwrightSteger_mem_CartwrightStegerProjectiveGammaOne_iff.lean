-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_mem_CartwrightStegerProjectiveGammaOne_iff
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.mem_CartwrightStegerProjectiveGammaOne_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:08:32.541505+00:00
-- url     : https://prove2.me/theorems/5db48ce6-6f29-45d5-85c1-242b4d2baa77
-- title:
--   Cartwright Steger: mem Cartwright Steger Projective Gamma One iff
-- statement:
--   The Cartwright Steger construction uses the mem Cartwright Steger Projective Gamma One iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/StrongApproximation.lean#L752-L758
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/StrongApproximation.lean#L752-L758

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.mem_CartwrightStegerProjectiveGammaOne_iff
    (P : BasePrime) (r : Rank)
    (g : CartwrightStegerOrderProjectiveGroup P r) :
    g ∈ CartwrightStegerProjectiveGammaOne P r ↔
      g ∈ CartwrightStegerOrderLattice P r ∧
        g ∈ CartwrightStegerProjectiveNormOne P r := by sorry
