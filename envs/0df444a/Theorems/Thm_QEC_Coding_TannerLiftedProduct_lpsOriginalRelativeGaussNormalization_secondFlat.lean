-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalization_secondFlat
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalization_secondFlat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T11:54:19.222397+00:00
-- url     : https://prove2.me/theorems/eedfe4d2-2213-4dfc-a377-512ca763032c
-- title:
--   Tanner Lifted Product: lps Original Relative Gauss Normalization second Flat
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Relative Gauss Normalization second Flat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussJointInteger.lean#L281-L288
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussJointInteger.lean#L281-L288

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussJointFiber
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussFricke
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussJointInteger
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped TensorProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalization_secondFlat
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    (lpsOriginalRelativeGaussNormalizationSecondOrderMap N p hNp h4N hN hpN).Flat := by sorry
