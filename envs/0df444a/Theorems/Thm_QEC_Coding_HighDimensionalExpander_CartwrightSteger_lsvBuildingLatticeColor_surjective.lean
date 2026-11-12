-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_lsvBuildingLatticeColor_surjective
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.lsvBuildingLatticeColor_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:01:27.802835+00:00
-- url     : https://prove2.me/theorems/26e77ece-8c74-45dd-9b35-f59aa4287063
-- title:
--   Cartwright Steger: lsv Building Lattice Color surjective
-- statement:
--   The lattice realizes every building-place color.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/FiniteSpectrum.lean#L117-L129
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/FiniteSpectrum.lean#L117-L129

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_QuotientComplex
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_UniversalBuildingSpectrum
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_FiniteSpectrum
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped BigOperators
open QEC.Coding.HighDimensionalExpander.SphericalHecke

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.lsvBuildingLatticeColor_surjective
    (P : BasePrime) (r : Rank) :
    Function.Surjective (lsvBuildingLatticeColor P r) := by sorry
