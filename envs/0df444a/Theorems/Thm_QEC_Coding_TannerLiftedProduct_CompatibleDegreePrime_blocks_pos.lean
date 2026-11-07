-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_CompatibleDegreePrime_blocks_pos
-- name    : QEC.Coding.TannerLiftedProduct.CompatibleDegreePrime.blocks_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:26:59.444035+00:00
-- url     : https://prove2.me/theorems/d18907cf-bcaf-459a-94d5-9ec4f9ca2ccd
-- title:
--   Compatible Degree Prime: blocks pos
-- statement:
--   The Compatible Degree Prime construction uses the blocks pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/CompatiblePrimeDegree.lean#L36-L41
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/CompatiblePrimeDegree.lean#L36-L41

import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Definitions.Def_QEC_Coding_ExpanderCodes_CompatiblePrimeDegree
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct

theorem QEC.Coding.TannerLiftedProduct.CompatibleDegreePrime.blocks_pos
    {A : Nat} (a : CompatibleDegreePrime A) (hA : 0 < A) :
    0 < a.blocks := by sorry
