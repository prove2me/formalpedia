-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_localDetOrder_quotient_of_orderUnit_mem_maximalCompact
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_localDetOrder_quotient_of_orderUnit_mem_maximalCompact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:43:38.808119+00:00
-- url     : https://prove2.me/theorems/33f30c62-8bd8-470e-bf35-4a1895ee6044
-- title:
--   Cartwright Steger: exists local Det Order quotient of order Unit mem maximal Compact
-- statement:
--   A projectively integral order unit has determinant order divisible by the
--   matrix rank.  The divisor is extracted from the actual projective scalar
--   relating it to an integral general-linear representative.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Projective/Stabilizer.lean#L274-L302
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Projective/Stabilizer.lean#L274-L302

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_LatticeBridge
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_RepresentationKernel
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_LocalLinkReduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_Stabilizer
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_localDetOrder_quotient_of_orderUnit_mem_maximalCompact
    (P : BasePrime) (r : Rank) (u : (CartwrightStegerOrder P r)ˣ)
    (hcompact : orderUnitToBuildingPGL P r u ∈
      SphericalHecke.maximalCompact (BaseField P) r.matrixRank) :
    ∃ q : ℤ,
      SphericalHecke.localUnitOrder
          (Matrix.GeneralLinearGroup.det
            (cyclicUnitToBuildingGL P r (orderUnitToCyclicUnit P r u))) =
        (r.matrixRank : ℤ) * q := by sorry
