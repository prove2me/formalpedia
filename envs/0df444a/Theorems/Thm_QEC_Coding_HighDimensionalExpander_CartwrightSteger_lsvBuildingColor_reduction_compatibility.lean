-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_lsvBuildingColor_reduction_compatibility
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.lsvBuildingColor_reduction_compatibility
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:44:24.085202+00:00
-- url     : https://prove2.me/theorems/3c366f6d-138f-4fc3-94f3-119e85372583
-- title:
--   Cartwright Steger: lsv Building Color reduction compatibility
-- statement:
--   Exact compatibility of building-place color and finite residue
--   determinant color on the entire constructed lattice.  The proof uses the
--   actual closure by Cartwright--Steger generators; it is not an assumed
--   commuting square.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/FiniteSpectrum.lean#L190-L233
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/FiniteSpectrum.lean#L190-L233

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_QuotientComplex
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_UniversalBuildingSpectrum
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_FiniteSpectrum
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped BigOperators
open QEC.Coding.HighDimensionalExpander.SphericalHecke

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.lsvBuildingColor_reduction_compatibility
    (P : BasePrime) (r : Rank) (level : Nat) :
    (lsvBuildingColorToResidueDetClass P r level).comp
        (lsvBuildingLatticeColor P r) =
      (indexImageDetClassHom P r level).comp
        (buildingLatticeReduction P r level) := by sorry
