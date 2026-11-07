-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_tprod_split_eq
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.tprod_split_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:12:58.213681+00:00
-- url     : https://prove2.me/theorems/70c1e6b4-0fe0-4bb6-b6e4-4cc5946dec5e
-- title:
--   Jacobi Triple Product Core: tprod split eq
-- statement:
--   The Jacobi Triple Product Core construction uses the tprod split eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L919-L936
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L919-L936

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.tprod_split_eq (k : ℕ) : letI := piTop;
    (∏' n, (1 - q ^ 2 * (q ^ 2) ^ n)) =
    (∏ i ∈ Finset.range k, (1 - q ^ 2 * (q ^ 2) ^ i)) *
    (∏' n, (1 - (q ^ 2 * (q ^ 2) ^ k) * (q ^ 2) ^ n)) := by sorry
