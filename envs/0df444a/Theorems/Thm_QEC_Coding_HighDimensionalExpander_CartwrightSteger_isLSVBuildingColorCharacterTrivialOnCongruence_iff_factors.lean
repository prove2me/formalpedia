-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_isLSVBuildingColorCharacterTrivialOnCongruence_iff_factors
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.isLSVBuildingColorCharacterTrivialOnCongruence_iff_factors
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:43:01.654755+00:00
-- url     : https://prove2.me/theorems/02de6eae-19da-4dd4-b0c6-45f313431d64
-- title:
--   Cartwright Steger: is LSVBuilding Color Character Trivial On Congruence iff factors
-- statement:
--   Exact bidirectional character descent.  Under the concrete `PSL`
--   containment, the one-dimensional building-color characters well defined on
--   the congruence quotient are precisely the pullbacks of characters of the
--   finite residue determinant-class quotient.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/FiniteSpectrum.lean#L391-L436
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/FiniteSpectrum.lean#L391-L436

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_QuotientComplex
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_UniversalBuildingSpectrum
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_FiniteSpectrum
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped BigOperators
open QEC.Coding.HighDimensionalExpander.SphericalHecke

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.isLSVBuildingColorCharacterTrivialOnCongruence_iff_factors
    (P : BasePrime) (r : Rank) (level : Nat)
    (hPSL : PSL P r level ≤ IndexCartwrightStegerImage P r level)
    (character : Multiplicative (ZMod r.matrixRank) →* ℂ) :
    IsLSVBuildingColorCharacterTrivialOnCongruence
        P r level character ↔
      ∃ finiteCharacter : ResiduePowerClass P r level →* ℂ,
        finiteCharacter.comp
            (lsvBuildingColorToResidueDetClass P r level) = character := by sorry
