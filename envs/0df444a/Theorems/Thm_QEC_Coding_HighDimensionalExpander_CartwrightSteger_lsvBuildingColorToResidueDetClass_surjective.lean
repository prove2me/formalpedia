-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_lsvBuildingColorToResidueDetClass_surjective
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.lsvBuildingColorToResidueDetClass_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:43:30.249241+00:00
-- url     : https://prove2.me/theorems/5d246b81-1317-41df-bc70-13f48853b091
-- title:
--   Cartwright Steger: lsv Building Color To Residue Det Class surjective
-- statement:
--   The building-to-residue color quotient is onto for every selected level.
--   This follows from the actual finite reduction and its determinant-class
--   surjectivity, together with the proved compatibility square.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/FiniteSpectrum.lean#L238-L247
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/FiniteSpectrum.lean#L238-L247

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_QuotientComplex
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_UniversalBuildingSpectrum
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_FiniteSpectrum
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped BigOperators
open QEC.Coding.HighDimensionalExpander.SphericalHecke

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.lsvBuildingColorToResidueDetClass_surjective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective (lsvBuildingColorToResidueDetClass P r level) := by sorry
