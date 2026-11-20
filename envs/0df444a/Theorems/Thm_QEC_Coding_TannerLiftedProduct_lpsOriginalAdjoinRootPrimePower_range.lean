-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalAdjoinRootPrimePower_range
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalAdjoinRootPrimePower_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:29:28.913519+00:00
-- url     : https://prove2.me/theorems/b711f1a0-01e6-4294-98d2-3530c6fa014c
-- title:
--   Tanner Lifted Product: lps Original Adjoin Root Prime Power range
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Adjoin Root Prime Power range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussBranches.lean#L215-L244
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussBranches.lean#L215-L244

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalAdjoinRootPrimePower_range
    {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (a : K)
    [Fact (Irreducible ((Polynomial.X : Polynomial K)^p - Polynomial.C a))]
    (x : AdjoinRoot ((Polynomial.X : Polynomial K)^p - Polynomial.C a)) :
    x^p ∈ (algebraMap K
      (AdjoinRoot ((Polynomial.X : Polynomial K)^p - Polynomial.C a))).range := by sorry
