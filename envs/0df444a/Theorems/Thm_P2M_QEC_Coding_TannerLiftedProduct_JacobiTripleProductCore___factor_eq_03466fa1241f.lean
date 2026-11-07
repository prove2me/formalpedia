-- Prove2me | Theorems.Thm_P2M_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore___factor_eq_03466fa1241f
-- name    : P2M_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore___factor_eq_03466fa1241f
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:15:16.574103+00:00
-- url     : https://prove2.me/theorems/8ef7e32b-ca70-4829-aa65-d6ff08223887
-- title:
--   P2 M QEC Coding Tanner Lifted Product Jacobi Triple Product Core   factor eq 03466fa1241f: P2 M QEC Coding Tanner Lifted Product Jacobi Triple Product Core   factor eq 03466fa1241f
-- statement:
--   The P2 M QEC Coding Tanner Lifted Product Jacobi Triple Product Core   factor eq 03466fa1241f construction uses the P2 M QEC Coding Tanner Lifted Product Jacobi Triple Product Core   factor eq 03466fa1241f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1535-L1542
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1535-L1542

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem P2M_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore___factor_eq_03466fa1241f (ℓ : ℕ) :
    ι_hahn (1 - q ^ (2 * (↑ℓ + 1))) = 1 - Q₀ ^ (ℓ + 1) := by sorry

alias «QEC».«Coding».«TannerLiftedProduct».«JacobiTripleProductCore».«ι_factor_eq» := P2M_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore___factor_eq_03466fa1241f
