-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_exists_compatibleDegreePrime_nthRoot_ge
-- name    : QEC.Coding.TannerLiftedProduct.exists_compatibleDegreePrime_nthRoot_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:27:05.633146+00:00
-- url     : https://prove2.me/theorems/5a7deba5-ec0f-46d3-9eb3-aa0d3946e5e8
-- title:
--   Tanner Lifted Product: exists compatible Degree Prime nth Root ge
-- statement:
--   The compatible prime can be chosen so that the floored sixth root of its
--   block quotient exceeds any prescribed scale.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/CompatiblePrimeDegree.lean#L121-L133
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/CompatiblePrimeDegree.lean#L121-L133

import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Definitions.Def_QEC_Coding_ExpanderCodes_CompatiblePrimeDegree
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct

theorem QEC.Coding.TannerLiftedProduct.exists_compatibleDegreePrime_nthRoot_ge
    (A target : Nat) (hA : 0 < A) (hOdd : Odd A) :
    ∃ a : CompatibleDegreePrime A,
      target ≤ Nat.nthRoot 6 a.blocks := by sorry
