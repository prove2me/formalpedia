-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCyclotomicReduction_root
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCyclotomicReduction_root
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:31:00.362084+00:00
-- url     : https://prove2.me/theorems/43380334-45ad-428d-9b03-32bf251108aa
-- title:
--   Tanner Lifted Product: lps Original Cyclotomic Reduction root
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Cyclotomic Reduction root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCyclotomicCoefficients.lean#L62-L64
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCyclotomicCoefficients.lean#L62-L64

import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCyclotomicCoefficients
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCyclotomicReduction_root (p : ℕ) [Fact p.Prime] :
    lpsOriginalCyclotomicReduction p (AdjoinRoot.root (Polynomial.cyclotomic p ℤ))=1 := by sorry
