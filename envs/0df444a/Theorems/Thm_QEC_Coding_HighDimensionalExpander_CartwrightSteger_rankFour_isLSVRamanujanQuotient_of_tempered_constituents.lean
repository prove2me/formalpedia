-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_rankFour_isLSVRamanujanQuotient_of_tempered_constituents
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.rankFour_isLSVRamanujanQuotient_of_tempered_constituents
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:56:04.590947+00:00
-- url     : https://prove2.me/theorems/642786ba-efc8-429f-b4d3-11597c10a1b4
-- title:
--   Cartwright Steger: rank Four is LSVRamanujan Quotient of tempered constituents
-- statement:
--   Forward rank-four adapter consumed downstream after temperedness has
--   been proved for every actual relevant constituent.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/RamanujanCriterion.lean#L244-L262
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/RamanujanCriterion.lean#L244-L262

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_PrefixHeckeCompatibility
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_QuotientL2
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_RamanujanCriterion
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open QEC.Coding.HighDimensionalExpander.SphericalHecke
universe u

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.rankFour_isLSVRamanujanQuotient_of_tempered_constituents
    (P : BasePrime) (level : Nat)
    (hLSV05aPropositionOneFive :
      IsLSVRamanujanQuotient P .four level ↔
        ∀ (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
          (sigma : Representation ℂ
            (HeckeGroup (BaseField P) Rank.four.matrixRank) V),
          IsLSVInfiniteDimensionalSphericalConstituent
              P .four level sigma →
            IsTempered sigma)
    (htempered :
      ∀ (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
        (sigma : Representation ℂ
          (HeckeGroup (BaseField P) Rank.four.matrixRank) V),
        IsLSVInfiniteDimensionalSphericalConstituent
            P .four level sigma →
          IsTempered sigma) :
    IsLSVRamanujanQuotient P .four level := by sorry
