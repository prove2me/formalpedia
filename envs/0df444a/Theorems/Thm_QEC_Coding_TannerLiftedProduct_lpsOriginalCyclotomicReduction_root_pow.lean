-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCyclotomicReduction_root_pow
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCyclotomicReduction_root_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:46:45.271554+00:00
-- url     : https://prove2.me/theorems/dcc7f277-0c99-49c9-b19d-d357f265e3ea
-- title:
--   Tanner Lifted Product: lps Original Cyclotomic Reduction root pow
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Cyclotomic Reduction root pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCyclotomicCoefficients.lean#L66-L69
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCyclotomicCoefficients.lean#L66-L69

import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCyclotomicCoefficients
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCyclotomicReduction_root_pow (p : ℕ) [Fact p.Prime] (m : ℕ) :
    lpsOriginalCyclotomicReduction p
      ((AdjoinRoot.root (Polynomial.cyclotomic p ℤ))^m)=1 := by sorry
