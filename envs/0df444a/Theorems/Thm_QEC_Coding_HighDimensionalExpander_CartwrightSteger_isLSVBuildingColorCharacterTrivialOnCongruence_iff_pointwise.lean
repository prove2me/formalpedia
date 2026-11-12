-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_isLSVBuildingColorCharacterTrivialOnCongruence_iff_pointwise
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.isLSVBuildingColorCharacterTrivialOnCongruence_iff_pointwise
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:42:19.631897+00:00
-- url     : https://prove2.me/theorems/0fbe6740-7ef3-41ce-93b1-daa77bd525ab
-- title:
--   Cartwright Steger: is LSVBuilding Color Character Trivial On Congruence iff pointwise
-- statement:
--   The Cartwright Steger construction uses the is LSVBuilding Color Character Trivial On Congruence iff pointwise property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/FiniteSpectrum.lean#L371-L385
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/FiniteSpectrum.lean#L371-L385

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_QuotientComplex
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_UniversalBuildingSpectrum
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_FiniteSpectrum
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped BigOperators
open QEC.Coding.HighDimensionalExpander.SphericalHecke

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.isLSVBuildingColorCharacterTrivialOnCongruence_iff_pointwise
    (P : BasePrime) (r : Rank) (level : Nat)
    (character : Multiplicative (ZMod r.matrixRank) →* ℂ) :
    IsLSVBuildingColorCharacterTrivialOnCongruence
        P r level character ↔
      ∀ g : BuildingCartwrightStegerCongruenceSubgroup P r level,
        character (lsvBuildingLatticeColor P r g.1) = 1 := by sorry
