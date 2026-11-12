-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_lsvMatrixRank_eq_congruenceColorOrder_mul_residueDetClassOrder
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.lsvMatrixRank_eq_congruenceColorOrder_mul_residueDetClassOrder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:01:18.251992+00:00
-- url     : https://prove2.me/theorems/32513df1-d1cb-434a-840c-d9a1f5a49c92
-- title:
--   Cartwright Steger: lsv Matrix Rank eq congruence Color Order mul residue Det Class Order
-- statement:
--   Exact order formula for the LSV notation.  If `t` is the cardinality of
--   the congruence subgroup's image in building color, then
--   `d = t * |ResiduePowerClass|`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/FiniteSpectrum.lean#L467-L503
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/FiniteSpectrum.lean#L467-L503

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_QuotientComplex
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_UniversalBuildingSpectrum
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_FiniteSpectrum
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped BigOperators
open QEC.Coding.HighDimensionalExpander.SphericalHecke

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.lsvMatrixRank_eq_congruenceColorOrder_mul_residueDetClassOrder
    (P : BasePrime) (r : Rank) (level : Nat)
    (hPSL : PSL P r level ≤ IndexCartwrightStegerImage P r level) :
    r.matrixRank =
      Nat.card (lsvCongruenceBuildingColorImage P r level) *
        orderOf
          (QuotientGroup.mk (indexRatioUnit P r level) :
            ResiduePowerClass P r level) := by sorry
