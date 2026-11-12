-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraBuildingNormOneGeneratorRatio_mem_splitNormOne
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraBuildingNormOneGeneratorRatio_mem_splitNormOne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:46:41.390956+00:00
-- url     : https://prove2.me/theorems/32410d9b-3339-456a-b3ef-b48c578bd08d
-- title:
--   Cartwright Steger: cyclic Algebra Building Norm One Generator Ratio mem split Norm One
-- statement:
--   The explicit generator ratio used at the building place also has
--   reduced norm one in the independent global splitting representation.  Thus
--   the nonidentity witness belongs simultaneously to both concrete kernels;
--   no equality of reduced norms from different splittings is assumed here.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/StrongApproximation.lean#L539-L556
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Arithmetic/StrongApproximation.lean#L539-L556

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraBuildingNormOneGeneratorRatio_mem_splitNormOne
    (P : BasePrime) (r : Rank)
    (u v : ConstantProjectiveClass P r) :
    (cyclicAlgebraBuildingNormOneGeneratorRatio P r u v :
        (CyclicAlgebra P r)ˣ) ∈ CyclicAlgebraSplitNormOne P r := by sorry
