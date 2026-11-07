-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalAffineDistinctPole
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalAffineDistinctPole
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:22:07.920208+00:00
-- url     : https://prove2.me/theorems/15aab893-e493-48ab-b42c-2359176b6a3f
-- title:
--   Tanner Lifted Product: lps Original Affine Distinct Pole
-- statement:
--   True zero-versus-one limits distinguish the actual smaller affine pole from original dilated j.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalExactStabilizer.lean#L87-L95
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalExactStabilizer.lean#L87-L95

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactStabilizer
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalAffineDistinctPole (m k : ℕ) (hm : 0<m)
    (hk : 0<k) (hmk : m<k) (r : ℝ) :
    ¬∀ τ : ℍ, lpsOriginalJInvariant (lpsE2AffineMatrix m hm r • τ)=
      lpsOriginalJDilated k hk τ := by sorry
