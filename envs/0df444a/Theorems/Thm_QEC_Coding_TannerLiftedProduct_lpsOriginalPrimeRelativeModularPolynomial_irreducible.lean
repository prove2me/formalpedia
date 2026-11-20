-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPrimeRelativeModularPolynomial_irreducible
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeRelativeModularPolynomial_irreducible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:18:42.08541+00:00
-- url     : https://prove2.me/theorems/3698c1bc-acb6-4e25-a60c-79ffac10f755
-- title:
--   Tanner Lifted Product: lps Original Prime Relative Modular Polynomial irreducible
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Prime Relative Modular Polynomial irreducible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeRelativeMinpoly.lean#L138-L147
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalPrimeRelativeMinpoly.lean#L138-L147

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeIntegralHeckeRelation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerLevelFunctionField
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeRelativeMinpoly
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalPrimeRelativeModularPolynomial_irreducible
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    Irreducible (lpsOriginalPrimeRelativeModularPolynomial N p hN
      (Fact.out : p.Prime).pos) := by sorry
