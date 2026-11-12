-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_rankThree_isLSVRamanujanQuotient_of_tempered_constituents
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.rankThree_isLSVRamanujanQuotient_of_tempered_constituents
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:55:33.826764+00:00
-- url     : https://prove2.me/theorems/cc31d426-f63d-4c14-a59c-42648e70d28a
-- title:
--   Cartwright Steger: rank Three is LSVRamanujan Quotient of tempered constituents
-- statement:
--   Forward rank-three adapter consumed downstream after temperedness has
--   been proved for every actual relevant constituent.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/RamanujanCriterion.lean#L201-L219
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/RamanujanCriterion.lean#L201-L219

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_PrefixHeckeCompatibility
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_QuotientL2
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_RamanujanCriterion
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open QEC.Coding.HighDimensionalExpander.SphericalHecke
universe u

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.rankThree_isLSVRamanujanQuotient_of_tempered_constituents
    (P : BasePrime) (level : Nat)
    (hLSV05aPropositionOneFive :
      IsLSVRamanujanQuotient P .three level ↔
        ∀ (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
          (sigma : Representation ℂ
            (HeckeGroup (BaseField P) Rank.three.matrixRank) V),
          IsLSVInfiniteDimensionalSphericalConstituent
              P .three level sigma →
            IsTempered sigma)
    (htempered :
      ∀ (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
        (sigma : Representation ℂ
          (HeckeGroup (BaseField P) Rank.three.matrixRank) V),
        IsLSVInfiniteDimensionalSphericalConstituent
            P .three level sigma →
          IsTempered sigma) :
    IsLSVRamanujanQuotient P .three level := by sorry
