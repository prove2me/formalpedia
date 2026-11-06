-- Prove2me | Theorems.Thm_QEC_Locality_bkRpowCoefficient_le_entropy_bound
-- name    : QEC.Locality.bkRpowCoefficient_le_entropy_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:07:38.730522+00:00
-- url     : https://prove2.me/theorems/7d2c0957-520f-46ad-9547-4a1ad6c15b00
-- title:
--   Locality: bk Rpow Coefficient le entropy bound
-- statement:
--   The exact coefficient is controlled explicitly by the entropy tangent gap.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/QuantitativeRecurrence.lean#L412-L440
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/QuantitativeRecurrence.lean#L412-L440

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

theorem QEC.Locality.bkRpowCoefficient_le_entropy_bound
    {beta c : ℝ} (hbeta : 0 ≤ beta) (hc0 : 0 ≤ c) (hc1 : c < 1) :
    bkRpowCoefficient beta c ≤
      3 * beta / (bkEntropyGap * (1 - c)) := by sorry
