-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalInteriorForgetLevel_fibre_card
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalInteriorForgetLevel_fibre_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:35:42.843682+00:00
-- url     : https://prove2.me/theorems/d7156cf3-80b3-483b-932a-8a8f0c508423
-- title:
--   Tanner Lifted Product: lps Original Interior Forget Level fibre card
-- statement:
--   Every actual interior fibre has cardinality the genuine relative subgroup index.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelFibres.lean#L185-L195
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalLevelFibres.lean#L185-L195

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelMapGeometry
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCosetCover
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelFibres
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane Manifold ContDiff
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalInteriorForgetLevel_fibre_card
    (N M : ℕ) (hNM : N ∣ M) (hN : 4 ∣ N)
    (y : MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) :
    Nat.card {x : MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ)) ℍ |
      lpsOriginalInteriorForgetLevel N M hNM x = y} =
      ((CongruenceSubgroup.Gamma0 M).subgroupOf
        (CongruenceSubgroup.Gamma0 N)).index := by sorry
