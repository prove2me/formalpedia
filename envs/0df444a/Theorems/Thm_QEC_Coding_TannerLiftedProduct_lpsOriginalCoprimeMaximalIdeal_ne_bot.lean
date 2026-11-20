-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCoprimeMaximalIdeal_ne_bot
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCoprimeMaximalIdeal_ne_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:28:09.103111+00:00
-- url     : https://prove2.me/theorems/d01bc848-641b-43d7-9d08-86bed5a2e028
-- title:
--   Tanner Lifted Product: lps Original Coprime Maximal Ideal ne bot
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Coprime Maximal Ideal ne bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussBranches.lean#L433-L439
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussBranches.lean#L433-L439

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCoprimeMaximalIdeal_ne_bot
    {R : Type*} [CommRing R] (I J : Ideal R) [J.IsMaximal]
    (hc : IsCoprime I J) : I ≠ ⊥ := by sorry
