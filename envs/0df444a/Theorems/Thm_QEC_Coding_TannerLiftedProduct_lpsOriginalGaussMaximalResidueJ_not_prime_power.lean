-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussMaximalResidueJ_not_prime_power
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalGaussMaximalResidueJ_not_prime_power
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:31:54.144183+00:00
-- url     : https://prove2.me/theorems/940e4692-108f-4a66-870e-c3df5622e042
-- title:
--   Tanner Lifted Product: lps Original Gauss Maximal Residue J not prime power
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Gauss Maximal Residue J not prime power property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGaussFirstResidueCoordinate.lean#L150-L167
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGaussFirstResidueCoordinate.lean#L150-L167

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussResidueCoordinate
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussFirstResidueCoordinate
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalGaussMaximalResidueJ_not_prime_power
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal]
    (u : LPSOriginalGaussAffineOrder N hN p ⧸ q) :
    u^p ≠ lpsOriginalGaussMaximalResidueJ N hN p q := by sorry
