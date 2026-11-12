-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_globalCyclicZMatrixHom_decomposition
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.globalCyclicZMatrixHom_decomposition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:23:18.020306+00:00
-- url     : https://prove2.me/theorems/8ad5ae5f-f0ba-494e-a6e3-dac96375f92e
-- title:
--   Cartwright Steger: global Cyclic ZMatrix Hom decomposition
-- statement:
--   Reduce an arbitrary integral power of the cyclic generator to its unique
--   residue exponent, with the quotient recorded by the central scalar `1 + y`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewFaithfulness.lean#L17-L72
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewFaithfulness.lean#L17-L72

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewResidueCoordinates
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewFaithfulness
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.globalCyclicZMatrixHom_decomposition
    (P : BasePrime) (r : Rank) (n : ℤ) :
    globalCyclicZMatrixHom P r (Multiplicative.ofAdd n) =
      (algebraMap (FunctionField P) (SplittingFunctionField P r)
        ((1 + RatFunc.X) ^ skewExponentQuotient r n)) •
        cyclicGeneratorMatrix P r ^ (skewExponentResidue r n : ℕ) := by sorry
