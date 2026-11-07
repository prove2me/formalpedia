-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCyclotomicRoot_pow
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCyclotomicRoot_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:31:01.185356+00:00
-- url     : https://prove2.me/theorems/b298fc51-9f5b-4f41-8a17-8a9ce682a654
-- title:
--   Tanner Lifted Product: lps Original Cyclotomic Root pow
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Cyclotomic Root pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCyclotomicCoefficients.lean#L76-L80
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCyclotomicCoefficients.lean#L76-L80

import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCyclotomicCoefficients
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCyclotomicRoot_pow (p : ℕ) [Fact p.Prime] :
    (AdjoinRoot.root (Polynomial.cyclotomic p ℤ))^p=1 := by sorry
