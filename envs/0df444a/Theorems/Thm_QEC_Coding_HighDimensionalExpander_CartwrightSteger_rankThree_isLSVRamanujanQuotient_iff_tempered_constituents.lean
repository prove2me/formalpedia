-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_rankThree_isLSVRamanujanQuotient_iff_tempered_constituents
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.rankThree_isLSVRamanujanQuotient_iff_tempered_constituents
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:54:54.506555+00:00
-- url     : https://prove2.me/theorems/e1be866e-5b1a-4ead-8cd7-ea5248b45777
-- title:
--   Cartwright Steger: rank Three is LSVRamanujan Quotient iff tempered constituents
-- statement:
--   Rank-three adapter for the exact LSV05a Proposition 1.5 equivalence.
--   The complete equivalence remains visible as a theorem argument.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/RamanujanCriterion.lean#L180-L197
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/Spectrum/RamanujanCriterion.lean#L180-L197

import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_PrefixHeckeCompatibility
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_QuotientL2
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Spectrum_RamanujanCriterion
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open QEC.Coding.HighDimensionalExpander.SphericalHecke
universe u

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.rankThree_isLSVRamanujanQuotient_iff_tempered_constituents
    (P : BasePrime) (level : Nat)
    (hLSV05aPropositionOneFive :
      IsLSVRamanujanQuotient P .three level ↔
        ∀ (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
          (sigma : Representation ℂ
            (HeckeGroup (BaseField P) Rank.three.matrixRank) V),
          IsLSVInfiniteDimensionalSphericalConstituent
              P .three level sigma →
            IsTempered sigma) :
    IsLSVRamanujanQuotient P .three level ↔
      ∀ (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
        (sigma : Representation ℂ
          (HeckeGroup (BaseField P) Rank.three.matrixRank) V),
        IsLSVInfiniteDimensionalSphericalConstituent
            P .three level sigma →
          IsTempered sigma := by sorry
