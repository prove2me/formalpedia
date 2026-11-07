-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPhaseCuspNumerator_map
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalPhaseCuspNumerator_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:13:51.822201+00:00
-- url     : https://prove2.me/theorems/ccdb63ed-4f6b-4fbf-a5b5-c8dc5402b320
-- title:
--   Tanner Lifted Product: lps Original Phase Cusp Numerator map
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Phase Cusp Numerator map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCosetCuspSeries.lean#L132-L140
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCosetCuspSeries.lean#L132-L140

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspPhaseResidue
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspSeriesReduction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCosetCuspSeries
set_option autoImplicit false
open Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
attribute [local instance] lpsOriginalLevelPhasePrime_isMaximal
attribute [local instance] lpsOriginalLevelPhaseResidue_field

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalPhaseCuspNumerator_map
    (R S : Type*) [CommRing R] [CommRing S] (f : R →+* S)
    (N m : ℕ) (hm : m ≠ 0) (ζ : R) :
    PowerSeries.map f (lpsOriginalPhaseCuspNumerator R N m hm ζ) =
      lpsOriginalPhaseCuspNumerator S N m hm (f ζ) := by sorry
