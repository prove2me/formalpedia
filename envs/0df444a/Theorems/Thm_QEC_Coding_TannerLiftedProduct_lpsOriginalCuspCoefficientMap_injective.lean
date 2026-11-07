-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCuspCoefficientMap_injective
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCuspCoefficientMap_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:23:29.564429+00:00
-- url     : https://prove2.me/theorems/5bc3908d-e084-4796-9b46-0a1127b3d296
-- title:
--   Tanner Lifted Product: lps Original Cusp Coefficient Map injective
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Cusp Coefficient Map injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspSeriesReduction.lean#L225-L237
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCuspSeriesReduction.lean#L225-L237

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerQExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCyclotomicCoefficients
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.Localization.Away.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspSeriesReduction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCuspCoefficientMap_injective {R S : Type*}
    [CommRing R] [CommRing S] [IsDomain S] (f : R →+* S) (hf : Function.Injective f) :
    Function.Injective (lpsOriginalCuspCoefficientMap f) := by sorry
