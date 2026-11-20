-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussHeckeBranchIdeals_product
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussHeckeBranchIdeals_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:27:52.28881+00:00
-- url     : https://prove2.me/theorems/1d1f6d03-9070-4b77-a9e8-68df908eb680
-- title:
--   Tanner Lifted Product: lps Original Relative Gauss Hecke Branch Ideals product
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Relative Gauss Hecke Branch Ideals product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussBranches.lean#L369-L387
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussBranches.lean#L369-L387

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussHeckeBranchIdeals_product
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    (LPSOriginalRelativeGaussHeckeLinearBranchIdeal N hN p hpN q) *
      (LPSOriginalRelativeGaussHeckeInseparableBranchIdeal N hN p hpN q) =
      q.map (AdjoinRoot.of (lpsOriginalRelativeGaussHeckePolynomial N hN p)) := by sorry
