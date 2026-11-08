-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsIntegerOffset_toNat_facts
-- name    : QEC.Coding.TannerLiftedProduct.lpsIntegerOffset_toNat_facts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:54:15.043774+00:00
-- url     : https://prove2.me/theorems/97b12bea-6cde-491b-aa59-9c387b435744
-- title:
--   Tanner Lifted Product: lps Integer Offset to Nat facts
-- statement:
--   The Tanner Lifted Product construction uses the lps Integer Offset to Nat facts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSTraceFirstCoordinateCount.lean#L81-L90
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSTraceFirstCoordinateCount.lean#L81-L90

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIntegerThreeSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionFactorization
import Mathlib.Algebra.Prime.Lemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceFirstCoordinateCount
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsIntegerOffset_toNat_facts (x : ℤ) (r M : ℕ)
    (hb : -(r : ℤ) ≤ x ∧ x ≤ (r : ℤ)) (hd : (M : ℤ) ∣ x+(r : ℤ)) :
    ((x+(r : ℤ)).toNat : ℤ)=x+(r : ℤ) ∧ (x+(r : ℤ)).toNat ≤ 2*r ∧
      M ∣ (x+(r : ℤ)).toNat := by sorry
