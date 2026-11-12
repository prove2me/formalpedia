-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_lsvResidueDetClassOrder_eq_matrixRank_div_congruenceColorOrder
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.lsvResidueDetClassOrder_eq_matrixRank_div_congruenceColorOrder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:47:51.062452+00:00
-- url     : https://prove2.me/theorems/19ad5818-ceed-41d4-8385-3c788459f0e8
-- title:
--   Cartwright Steger: lsv Residue Det Class Order eq matrix Rank div congruence Color Order
-- statement:
--   In the source's notation, the order of the surviving finite determinant
--   color quotient is literally `d / t`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/FiniteSpectrum.lean#L507-L530
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/FiniteSpectrum.lean#L507-L530

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_QuotientComplex
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_UniversalBuildingSpectrum
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_FiniteSpectrum
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped BigOperators
open QEC.Coding.HighDimensionalExpander.SphericalHecke

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.lsvResidueDetClassOrder_eq_matrixRank_div_congruenceColorOrder
    (P : BasePrime) (r : Rank) (level : Nat)
    (hPSL : PSL P r level ≤ IndexCartwrightStegerImage P r level) :
    r.matrixRank /
        Nat.card (lsvCongruenceBuildingColorImage P r level) =
      orderOf
        (QuotientGroup.mk (indexRatioUnit P r level) :
          ResiduePowerClass P r level) := by sorry
