-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussInseparableBranch_purelyInseparable
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussInseparableBranch_purelyInseparable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:28:57.561914+00:00
-- url     : https://prove2.me/theorems/385a7fee-e217-4871-9403-d59bb1203bcf
-- title:
--   Tanner Lifted Product: lps Original Relative Gauss Inseparable Branch purely Inseparable
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Relative Gauss Inseparable Branch purely Inseparable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussBranches.lean#L246-L264
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussBranches.lean#L246-L264

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussInseparableBranch_purelyInseparable
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    letI : Field (LPSOriginalGaussAffineOrder N hN p ⧸ q) := Ideal.Quotient.field q
    letI := lpsOriginalRelativeGaussInseparableBranch_field N hN p hpN q
    IsPurelyInseparable (LPSOriginalGaussAffineOrder N hN p ⧸ q)
      (LPSOriginalRelativeGaussInseparableBranch N hN p q) := by sorry
