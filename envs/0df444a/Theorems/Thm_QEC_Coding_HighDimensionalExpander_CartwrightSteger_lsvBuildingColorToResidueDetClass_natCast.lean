-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_lsvBuildingColorToResidueDetClass_natCast
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.lsvBuildingColorToResidueDetClass_natCast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:01:27.223204+00:00
-- url     : https://prove2.me/theorems/2dbc92c6-66cb-45b1-afeb-877d794c1c7c
-- title:
--   Cartwright Steger: lsv Building Color To Residue Det Class nat Cast
-- statement:
--   Evaluation of the building-to-residue color quotient on a natural color.
--   The selected ratio class is the image of color one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/FiniteSpectrum.lean#L440-L450
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/FiniteSpectrum.lean#L440-L450

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_QuotientComplex
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_UniversalBuildingSpectrum
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_FiniteSpectrum
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped BigOperators
open QEC.Coding.HighDimensionalExpander.SphericalHecke

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.lsvBuildingColorToResidueDetClass_natCast
    (P : BasePrime) (r : Rank) (level n : Nat) :
    lsvBuildingColorToResidueDetClass P r level
        (Multiplicative.ofAdd (n : ZMod r.matrixRank)) =
      (QuotientGroup.mk (indexRatioUnit P r level) :
        ResiduePowerClass P r level) ^ n := by sorry
