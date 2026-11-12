-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_isLSVRamanujanQuotient_iff
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.isLSVRamanujanQuotient_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:56:08.917968+00:00
-- url     : https://prove2.me/theorems/21140c25-aab1-4046-a548-3464a62bdc6f
-- title:
--   Cartwright Steger: is LSVRamanujan Quotient iff
-- statement:
--   The Cartwright Steger construction uses the is LSVRamanujan Quotient iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/RamanujanCriterion.lean#L168-L176
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/RamanujanCriterion.lean#L168-L176

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_PrefixHeckeCompatibility
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_QuotientL2
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_RamanujanCriterion
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open QEC.Coding.HighDimensionalExpander.SphericalHecke
universe u

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.isLSVRamanujanQuotient_iff
    (P : BasePrime) (r : Rank) (level : Nat) :
    IsLSVRamanujanQuotient P r level ↔
      ∀ eigenvalue vector,
        IsLSVJointEigenpair P r level eigenvalue vector →
        ¬ IsLSVFiniteDetCharacterVector P r level vector →
        eigenvalue ∈ lsvUniversalBuildingJointSpectrum P r := by sorry
