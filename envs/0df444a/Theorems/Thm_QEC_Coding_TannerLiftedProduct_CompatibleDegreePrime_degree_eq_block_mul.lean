-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_CompatibleDegreePrime_degree_eq_block_mul
-- name    : QEC.Coding.TannerLiftedProduct.CompatibleDegreePrime.degree_eq_block_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:40:27.840315+00:00
-- url     : https://prove2.me/theorems/d2d2b581-e729-4dfc-b0fb-f90a2f03a1f2
-- title:
--   Compatible Degree Prime: degree eq block mul
-- statement:
--   The Compatible Degree Prime construction uses the degree eq block mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/CompatiblePrimeDegree.lean#L30-L34
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/CompatiblePrimeDegree.lean#L30-L34

import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Definitions.Def_QEC_Coding_ExpanderCodes_CompatiblePrimeDegree
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct

theorem QEC.Coding.TannerLiftedProduct.CompatibleDegreePrime.degree_eq_block_mul
    {A : Nat} (a : CompatibleDegreePrime A) :
    a.p + 1 = A * a.blocks := by sorry
