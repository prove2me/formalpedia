-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussSecondJField_eq_secondPullback
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussSecondJField_eq_secondPullback
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:35:18.796214+00:00
-- url     : https://prove2.me/theorems/307fb8dd-cf6e-4c70-9bb6-38eccb6fb05b
-- title:
--   Tanner Lifted Product: lps Original Relative Gauss Second JField eq second Pullback
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Relative Gauss Second JField eq second Pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussSecondCoordinates.lean#L249-L257
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussSecondCoordinates.lean#L249-L257

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussNormalizationBranches
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalSecondIntegerHecke
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondCoordinates
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussSecondJField_eq_secondPullback
    (N p : ℕ) [NeZero N] [NeZero p] (h4N : 4 ∣ N) (hN : 0 < N) (hp : 0 < p) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    lpsOriginalRelativeGaussSecondJField N p h4N hN hp =
      lpsOriginalRationalFrickeLevelPullback N (N*p) (dvd_mul_right N p) h4N hN
        (Nat.mul_pos hN hp) (lpsOriginalRationalJElement N hN) := by sorry
