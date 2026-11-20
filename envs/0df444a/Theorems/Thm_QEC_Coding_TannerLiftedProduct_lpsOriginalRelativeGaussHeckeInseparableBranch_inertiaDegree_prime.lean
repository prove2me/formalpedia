-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussHeckeInseparableBranch_inertiaDegree_prime
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussHeckeInseparableBranch_inertiaDegree_prime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:27:23.815076+00:00
-- url     : https://prove2.me/theorems/58c53fa9-d46f-4313-8f8f-36474b82da91
-- title:
--   Tanner Lifted Product: lps Original Relative Gauss Hecke Inseparable Branch inertia Degree prime
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Relative Gauss Hecke Inseparable Branch inertia Degree prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussBranches.lean#L565-L575
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussBranches.lean#L565-L575

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussHeckeInseparableBranch_inertiaDegree_prime
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    (LPSOriginalRelativeGaussHeckeInseparableBranchIdeal N hN p hpN q).inertiaDeg
      (LPSOriginalGaussAffineOrder N hN p) = p := by sorry
