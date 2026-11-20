-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussHeckeLinearBranch_inertiaDegree_one
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussHeckeLinearBranch_inertiaDegree_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:28:59.671314+00:00
-- url     : https://prove2.me/theorems/0422d479-23e9-412b-be41-30e341fb8722
-- title:
--   Tanner Lifted Product: lps Original Relative Gauss Hecke Linear Branch inertia Degree one
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Relative Gauss Hecke Linear Branch inertia Degree one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussBranches.lean#L553-L563
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussBranches.lean#L553-L563

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussHeckeLinearBranch_inertiaDegree_one
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal] :
    (LPSOriginalRelativeGaussHeckeLinearBranchIdeal N hN p hpN q).inertiaDeg
      (LPSOriginalGaussAffineOrder N hN p) = 1 := by sorry
