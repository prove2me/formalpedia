-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPhaseCuspSeries_clear
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalPhaseCuspSeries_clear
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:13:14.563395+00:00
-- url     : https://prove2.me/theorems/517091ba-5236-4834-9432-36ce15d67927
-- title:
--   Tanner Lifted Product: lps Original Phase Cusp Series clear
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Phase Cusp Series clear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCosetCuspSeries.lean#L57-L67
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCosetCuspSeries.lean#L57-L67

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalPhaseCuspSeries_clear
    (R : Type*) [CommRing R] (N m : ℕ) (hm : m ≠ 0) (ζ : R)
    (D : ℕ) (hD : m ≤ D) :
    (algebraMap (PowerSeries R) (lpsOriginalCuspSeriesRing R) PowerSeries.X)^D *
      lpsOriginalPhaseCuspSeries R N m hm ζ =
      algebraMap (PowerSeries R) (lpsOriginalCuspSeriesRing R)
        (PowerSeries.X^(D-m) * lpsOriginalPhaseCuspNumerator R N m hm ζ) := by sorry
