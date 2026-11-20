-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussHeckePrimeOver_classification
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussHeckePrimeOver_classification
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:27:12.149238+00:00
-- url     : https://prove2.me/theorems/10e639a3-154a-42d3-9ab1-e57bbdb2a1da
-- title:
--   Tanner Lifted Product: lps Original Relative Gauss Hecke Prime Over classification
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Relative Gauss Hecke Prime Over classification property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussBranches.lean#L579-L593
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussBranches.lean#L579-L593

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussHeckePrimeOver_classification
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N)
    (q : Ideal (LPSOriginalGaussAffineOrder N hN p)) [q.IsMaximal]
    (P : Ideal (LPSOriginalRelativeGaussHeckeOrder N hN p)) [P.IsPrime] [P.LiesOver q] :
    P = LPSOriginalRelativeGaussHeckeLinearBranchIdeal N hN p hpN q ∨
      P = LPSOriginalRelativeGaussHeckeInseparableBranchIdeal N hN p hpN q := by sorry
