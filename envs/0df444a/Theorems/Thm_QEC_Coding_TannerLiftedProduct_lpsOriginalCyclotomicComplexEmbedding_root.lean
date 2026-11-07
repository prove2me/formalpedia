-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCyclotomicComplexEmbedding_root
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCyclotomicComplexEmbedding_root
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:30:47.594604+00:00
-- url     : https://prove2.me/theorems/0d974795-8c4b-476f-9974-0fe932429b26
-- title:
--   Tanner Lifted Product: lps Original Cyclotomic Complex Embedding root
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Cyclotomic Complex Embedding root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCyclotomicCoefficients.lean#L71-L74
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCyclotomicCoefficients.lean#L71-L74

import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCyclotomicCoefficients
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCyclotomicComplexEmbedding_root (p : ℕ) [Fact p.Prime] :
    lpsOriginalCyclotomicComplexEmbedding p (AdjoinRoot.root (Polynomial.cyclotomic p ℤ))=
      lpsOriginalCyclotomicComplexRoot p := by sorry
