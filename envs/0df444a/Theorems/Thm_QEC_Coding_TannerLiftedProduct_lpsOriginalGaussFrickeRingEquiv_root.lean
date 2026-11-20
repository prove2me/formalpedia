-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussFrickeRingEquiv_root
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalGaussFrickeRingEquiv_root
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T11:16:21.714737+00:00
-- url     : https://prove2.me/theorems/01467592-a2f4-4254-a286-5a71cc176b01
-- title:
--   Tanner Lifted Product: lps Original Gauss Fricke Ring Equiv root
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Gauss Fricke Ring Equiv root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGaussFricke.lean#L167-L171
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGaussFricke.lean#L167-L171

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondOrderMap
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussFricke
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalGaussFrickeRingEquiv_root
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) :
    lpsOriginalGaussFrickeRingEquiv N hN p hpN (AdjoinRoot.root (lpsOriginalGaussPolynomial N hN p)) = AdjoinRoot.of (lpsOriginalGaussPolynomial N hN p)
        (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) Polynomial.X) := by sorry
