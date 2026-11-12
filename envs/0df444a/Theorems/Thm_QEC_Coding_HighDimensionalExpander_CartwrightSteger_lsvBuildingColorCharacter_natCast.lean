-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_lsvBuildingColorCharacter_natCast
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.lsvBuildingColorCharacter_natCast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:02:45.188203+00:00
-- url     : https://prove2.me/theorems/3367193d-a72c-4b56-9e83-4f1ef4d98119
-- title:
--   Cartwright Steger: lsv Building Color Character nat Cast
-- statement:
--   Evaluation of a building-color character on a natural color.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/FiniteSpectrum.lean#L453-L462
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/FiniteSpectrum.lean#L453-L462

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_QuotientComplex
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_UniversalBuildingSpectrum
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_FiniteSpectrum
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped BigOperators
open QEC.Coding.HighDimensionalExpander.SphericalHecke

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.lsvBuildingColorCharacter_natCast
    (r : Rank) (character : Multiplicative (ZMod r.matrixRank) →* ℂ)
    (n : Nat) :
    character (Multiplicative.ofAdd (n : ZMod r.matrixRank)) =
      character (Multiplicative.ofAdd (1 : ZMod r.matrixRank)) ^ n := by sorry
