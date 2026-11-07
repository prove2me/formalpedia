-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiLambertTerm
-- name    : QEC.Coding.TannerLiftedProduct.coeff_jacobiLambertTerm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:18:16.525247+00:00
-- url     : https://prove2.me/theorems/91c68d7e-b74f-4648-8d56-a0c7d4e950a4
-- title:
--   Tanner Lifted Product: coeff jacobi Lambert Term
-- statement:
--   The Tanner Lifted Product construction uses the coeff jacobi Lambert Term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiLambertSeries.lean#L318-L321
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiLambertSeries.lean#L318-L321

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiThetaProduct
import Mathlib.RingTheory.PowerSeries.WellKnown
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiLambertSeries
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset PowerSeries
open scoped PowerSeries.WithPiTopology Topology

theorem QEC.Coding.TannerLiftedProduct.coeff_jacobiLambertTerm (d n : ℕ) :
    PowerSeries.coeff n (jacobiLambertTerm d) =
      if 0 < n ∧ d ∣ n then (d : ℚ) else 0 := by sorry
