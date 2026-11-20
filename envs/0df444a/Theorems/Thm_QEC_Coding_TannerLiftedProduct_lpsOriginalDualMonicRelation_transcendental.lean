-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalDualMonicRelation_transcendental
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalDualMonicRelation_transcendental
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:01:10.409554+00:00
-- url     : https://prove2.me/theorems/05fea6ab-9072-4349-9416-f0f9cd4d0e35
-- title:
--   Tanner Lifted Product: lps Original Dual Monic Relation transcendental
-- statement:
--   a monic dual relation transfers transcendence.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegralDualRelation.lean#L202-L227
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegralDualRelation.lean#L202-L227

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeIntegralHeckeRelation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussSpecialFiber
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralDualRelation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalDualMonicRelation_transcendental
    (F K : Type*) [Field F] [Field K] [Algebra F K]
    (P : Polynomial (Polynomial F)) (hP : P.Monic)
    (x y : K)
    (hroot : P.eval₂ (Polynomial.eval₂RingHom (algebraMap F K) y) x = 0)
    (hx : Transcendental F x) : Transcendental F y := by sorry
