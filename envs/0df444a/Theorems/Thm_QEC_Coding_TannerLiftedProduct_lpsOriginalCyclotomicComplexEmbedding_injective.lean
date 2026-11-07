-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCyclotomicComplexEmbedding_injective
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalCyclotomicComplexEmbedding_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:30:59.013203+00:00
-- url     : https://prove2.me/theorems/6af1652d-2093-47ea-9a72-0ea1e35de1d5
-- title:
--   Tanner Lifted Product: lps Original Cyclotomic Complex Embedding injective
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Cyclotomic Complex Embedding injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCyclotomicCoefficients.lean#L39-L50
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalCyclotomicCoefficients.lean#L39-L50

import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCyclotomicCoefficients
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalCyclotomicComplexEmbedding_injective (p : ℕ) [Fact p.Prime] :
    Function.Injective (lpsOriginalCyclotomicComplexEmbedding p) := by sorry
