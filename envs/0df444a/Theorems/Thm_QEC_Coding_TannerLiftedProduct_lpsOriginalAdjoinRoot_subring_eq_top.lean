-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalAdjoinRoot_subring_eq_top
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalAdjoinRoot_subring_eq_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T11:56:38.430168+00:00
-- url     : https://prove2.me/theorems/171f2803-bcd2-4a91-978c-0c959f38ff56
-- title:
--   Tanner Lifted Product: lps Original Adjoin Root subring eq top
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Adjoin Root subring eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussJointInteger.lean#L30-L40
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussJointInteger.lean#L30-L40

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussJointFiber
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussFricke
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussJointInteger
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped TensorProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalAdjoinRoot_subring_eq_top
    {R : Type*} [CommRing R] (f : Polynomial R) (S : Subring (AdjoinRoot f))
    (hcoeff : ∀ r : R, AdjoinRoot.of f r ∈ S) (hroot : AdjoinRoot.root f ∈ S) : S = ⊤ := by sorry
