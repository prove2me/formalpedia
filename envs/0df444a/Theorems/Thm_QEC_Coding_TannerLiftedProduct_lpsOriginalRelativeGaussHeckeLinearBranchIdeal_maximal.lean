-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussHeckeLinearBranchIdeal_maximal
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussHeckeLinearBranchIdeal_maximal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:27:04.938199+00:00
-- url     : https://prove2.me/theorems/69a8b31d-9d86-4314-9d90-256768cda9d1
-- title:
--   Tanner Lifted Product: lps Original Relative Gauss Hecke Linear Branch Ideal maximal
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Relative Gauss Hecke Linear Branch Ideal maximal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussBranches.lean#L344-L350
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussBranches.lean#L344-L350

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussHeckeLinearBranchIdeal_maximal
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    (LPSOriginalRelativeGaussHeckeLinearBranchIdeal N hN p hpN q).IsMaximal := by sorry
