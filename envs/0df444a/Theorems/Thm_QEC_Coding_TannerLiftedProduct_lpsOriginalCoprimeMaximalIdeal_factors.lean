-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCoprimeMaximalIdeal_factors
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCoprimeMaximalIdeal_factors
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:29:34.189218+00:00
-- url     : https://prove2.me/theorems/edeb17cb-caef-4645-aafa-d85b053c4e12
-- title:
--   Tanner Lifted Product: lps Original Coprime Maximal Ideal factors
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Coprime Maximal Ideal factors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussBranches.lean#L441-L452
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussBranches.lean#L441-L452

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCoprimeMaximalIdeal_factors
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    (I J : Ideal R) [I.IsMaximal] [J.IsMaximal] (hc : IsCoprime I J) :
    UniqueFactorizationMonoid.normalizedFactors (I*J) = {I} + {J} := by sorry
