-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_isLSVBuildingColorCharacterTrivialOnCongruence_iff_zeta_pow
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.isLSVBuildingColorCharacterTrivialOnCongruence_iff_zeta_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:46:19.706524+00:00
-- url     : https://prove2.me/theorems/f976c455-b5b8-49f8-9822-c1b454cccf75
-- title:
--   Cartwright Steger: is LSVBuilding Color Character Trivial On Congruence iff zeta pow
-- statement:
--   Literal LSV05a descent criterion.  Write `t` for the order of the color
--   image of the congruence subgroup.  The finite residue determinant class has
--   order `d / t`; hence the displayed exponent is exactly the paper's
--   `d/t`.  The proof is bidirectional and uses the exact color-image/kernel
--   identity above, not an unrestricted `ζ^d = 1` condition.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/FiniteSpectrum.lean#L537-L596
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/FiniteSpectrum.lean#L537-L596

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_QuotientComplex
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_UniversalBuildingSpectrum
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_FiniteSpectrum
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped BigOperators
open QEC.Coding.HighDimensionalExpander.SphericalHecke

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.isLSVBuildingColorCharacterTrivialOnCongruence_iff_zeta_pow
    (P : BasePrime) (r : Rank) (level : Nat)
    (hPSL : PSL P r level ≤ IndexCartwrightStegerImage P r level)
    (character : Multiplicative (ZMod r.matrixRank) →* ℂ) :
    IsLSVBuildingColorCharacterTrivialOnCongruence
        P r level character ↔
      character (Multiplicative.ofAdd (1 : ZMod r.matrixRank)) ^
          orderOf
            (QuotientGroup.mk (indexRatioUnit P r level) :
              ResiduePowerClass P r level) = 1 := by sorry
