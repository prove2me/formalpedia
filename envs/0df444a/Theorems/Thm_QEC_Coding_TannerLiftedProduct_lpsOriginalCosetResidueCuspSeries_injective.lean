-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCosetResidueCuspSeries_injective
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCosetResidueCuspSeries_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:20:48.192527+00:00
-- url     : https://prove2.me/theorems/f02e5f07-0892-4152-b808-ded3b93e483f
-- title:
--   Tanner Lifted Product: lps Original Coset Residue Cusp Series injective
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Coset Residue Cusp Series injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCosetCuspSeries.lean#L191-L204
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCosetCuspSeries.lean#L191-L204

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCosetResidueCuspSeries_injective
    (N : ℕ) (hN : 0 < N) (p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N) :
    Function.Injective (lpsOriginalCosetResidueCuspSeries N hN p hp) := by sorry
