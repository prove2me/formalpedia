-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussInseparableBranch_finrank
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussInseparableBranch_finrank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:29:26.302075+00:00
-- url     : https://prove2.me/theorems/3b734e25-2a36-47af-9e33-1fe29ad15a3e
-- title:
--   Tanner Lifted Product: lps Original Relative Gauss Inseparable Branch finrank
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Relative Gauss Inseparable Branch finrank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussBranches.lean#L86-L99
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussBranches.lean#L86-L99

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussNormalization
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussBranches
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussInseparableBranch_finrank
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime]
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    Module.finrank (LPSOriginalGaussAffineOrder N hN p ⧸ q)
      (LPSOriginalRelativeGaussInseparableBranch N hN p q) = p := by sorry
