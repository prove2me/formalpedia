-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussMaximalResidueJN_not_prime_power
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalGaussMaximalResidueJN_not_prime_power
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:26:12.702185+00:00
-- url     : https://prove2.me/theorems/15830ac4-322d-4342-a58d-142bfae61954
-- title:
--   Tanner Lifted Product: lps Original Gauss Maximal Residue JN not prime power
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Gauss Maximal Residue JN not prime power property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGaussResidueCoordinate.lean#L410-L427
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalGaussResidueCoordinate.lean#L410-L427

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegralDualRelation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeGaussNormality
import Mathlib.FieldTheory.SeparableDegree
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussResidueCoordinate
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalGaussMaximalResidueJN_not_prime_power
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal]
    (u : LPSOriginalGaussAffineOrder N hN p ⧸ q) :
    u^p ≠ lpsOriginalGaussMaximalResidueJN N hN p q := by sorry
