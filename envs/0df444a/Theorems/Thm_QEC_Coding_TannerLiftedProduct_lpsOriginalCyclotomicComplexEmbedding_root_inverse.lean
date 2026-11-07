-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCyclotomicComplexEmbedding_root_inverse
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCyclotomicComplexEmbedding_root_inverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:46:56.758572+00:00
-- url     : https://prove2.me/theorems/602d6f37-e52e-4f54-a7a7-28b469a507a7
-- title:
--   Tanner Lifted Product: lps Original Cyclotomic Complex Embedding root inverse
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Cyclotomic Complex Embedding root inverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCyclotomicCoefficients.lean#L88-L93
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCyclotomicCoefficients.lean#L88-L93

import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCyclotomicCoefficients
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCyclotomicComplexEmbedding_root_inverse (p : ℕ) [Fact p.Prime] :
    lpsOriginalCyclotomicComplexEmbedding p ((AdjoinRoot.root (Polynomial.cyclotomic p ℤ))^(p-1))=
      (lpsOriginalCyclotomicComplexRoot p)⁻¹ := by sorry
