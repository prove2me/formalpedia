-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussHeckeInseparableBranch_ramificationIndex_one
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussHeckeInseparableBranch_ramificationIndex_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:28:55.50629+00:00
-- url     : https://prove2.me/theorems/ad0fc7e5-5fb8-4bad-8b1c-112d14c66b71
-- title:
--   Tanner Lifted Product: lps Original Relative Gauss Hecke Inseparable Branch ramification Index one
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Relative Gauss Hecke Inseparable Branch ramification Index one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussBranches.lean#L497-L512
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussBranches.lean#L497-L512

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussHeckeInseparableBranch_ramificationIndex_one
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    (LPSOriginalRelativeGaussHeckeInseparableBranchIdeal N hN p hpN q).ramificationIdx
      (LPSOriginalGaussAffineOrder N hN p) = 1 := by sorry
