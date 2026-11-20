-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalAdjoinRootPrimePower_root
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalAdjoinRootPrimePower_root
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:27:07.529074+00:00
-- url     : https://prove2.me/theorems/0fa1eb8c-7a2d-4dad-b0a8-35f1364ba4c1
-- title:
--   Tanner Lifted Product: lps Original Adjoin Root Prime Power root
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Adjoin Root Prime Power root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussBranches.lean#L208-L213
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussBranches.lean#L208-L213

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalAdjoinRootPrimePower_root
    {K : Type*} [CommRing K] (p : ℕ) (a : K) :
    let Q : Polynomial K := Polynomial.X^p - Polynomial.C a
    (AdjoinRoot.root Q)^p = AdjoinRoot.of Q a := by sorry
