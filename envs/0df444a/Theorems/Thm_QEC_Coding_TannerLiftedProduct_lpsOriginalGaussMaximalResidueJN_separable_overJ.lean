-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussMaximalResidueJN_separable_overJ
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalGaussMaximalResidueJN_separable_overJ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:30:37.55676+00:00
-- url     : https://prove2.me/theorems/dd7ae317-eaed-4344-bf79-03e1c2ad784f
-- title:
--   Tanner Lifted Product: lps Original Gauss Maximal Residue JN separable over J
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Gauss Maximal Residue JN separable over J property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGaussFirstResidueCoordinate.lean#L75-L88
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGaussFirstResidueCoordinate.lean#L75-L88

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussResidueCoordinate
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussFirstResidueCoordinate
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalGaussMaximalResidueJN_separable_overJ
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
    letI := (lpsOriginalGaussMaximalResidueFractionMap N hN p q).toAlgebra
    IsSeparable (FractionRing (Polynomial (ZMod p)))
      (lpsOriginalGaussMaximalResidueJN N hN p q) := by sorry
