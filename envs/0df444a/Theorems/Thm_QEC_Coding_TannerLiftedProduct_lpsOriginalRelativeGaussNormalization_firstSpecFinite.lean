-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussNormalization_firstSpecFinite
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalization_firstSpecFinite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T11:54:20.684199+00:00
-- url     : https://prove2.me/theorems/30e8c942-54e5-4141-a934-f4c69a0b0ea1
-- title:
--   Tanner Lifted Product: lps Original Relative Gauss Normalization first Spec Finite
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Relative Gauss Normalization first Spec Finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussJointInteger.lean#L262-L271
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussJointInteger.lean#L262-L271

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussJointFiber
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussFricke
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussJointInteger
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped TensorProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussNormalization_firstSpecFinite
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N) :
    AlgebraicGeometry.IsFinite (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
      (lpsOriginalRelativeGaussNormalizationCoefficients N p hNp h4N hN hpN))) := by sorry
