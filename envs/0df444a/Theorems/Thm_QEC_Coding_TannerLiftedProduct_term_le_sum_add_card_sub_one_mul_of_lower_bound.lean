-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_term_le_sum_add_card_sub_one_mul_of_lower_bound
-- name    : QEC.Coding.TannerLiftedProduct.term_le_sum_add_card_sub_one_mul_of_lower_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:58:01.707325+00:00
-- url     : https://prove2.me/theorems/8de1a4c4-d736-4dff-9c9a-8823eb3ae55c
-- title:
--   Tanner Lifted Product: term le sum add card sub one mul of lower bound
-- statement:
--   If every term in a finite real sum is at least `-B`, no individual
--   term can exceed the total by more than the worst possible contribution of
--   the remaining terms.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRamanujanTraceBridge.lean#L24-L40
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRamanujanTraceBridge.lean#L24-L40

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSExactTraceFormula
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSpectralTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRamanujanTraceBridge
set_option autoImplicit false
open Polynomial
open scoped MatrixGroups
open Filter Asymptotics
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.term_le_sum_add_card_sub_one_mul_of_lower_bound
    {I : Type*} [Fintype I] [DecidableEq I]
    (f : I → ℝ) (B : ℝ) (i : I)
    (hLower : ∀ j, -B ≤ f j) :
    f i ≤ ∑ j, f j + ((Fintype.card I - 1 : ℕ) : ℝ) * B := by sorry
