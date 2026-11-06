-- Prove2me | Theorems.Thm_QEC_Locality_bkRpowPotential_eq_source_form
-- name    : QEC.Locality.bkRpowPotential_eq_source_form
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:16:16.007019+00:00
-- url     : https://prove2.me/theorems/a62047e0-22a9-4806-80e2-bc7fc793e484
-- title:
--   Locality: bk Rpow Potential eq source form
-- statement:
--   The normalized potential is exactly the source's linear-minus-power expression.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/QuantitativeRecurrence.lean#L229-L264
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/QuantitativeRecurrence.lean#L229-L264

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_SumPreservingRecurrence
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_QuantitativeRecurrence
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open Set
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.bkRpowPotential_eq_source_form
    {beta c : ℝ} {d parent : Nat} (hd : 0 < d) :
    bkRpowPotential beta c d parent =
      bkRpowCoefficient beta c * parent / (d : ℝ) ^ (1 - c) -
        (beta / bkRpowGap c) * (parent : ℝ) ^ c := by sorry
