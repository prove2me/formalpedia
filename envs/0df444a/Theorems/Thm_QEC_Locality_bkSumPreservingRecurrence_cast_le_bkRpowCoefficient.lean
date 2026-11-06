-- Prove2me | Theorems.Thm_QEC_Locality_bkSumPreservingRecurrence_cast_le_bkRpowCoefficient
-- name    : QEC.Locality.bkSumPreservingRecurrence_cast_le_bkRpowCoefficient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:15:57.583254+00:00
-- url     : https://prove2.me/theorems/80f7b1fa-1791-445d-91a6-bfcf05bcd444
-- title:
--   Locality: bk Sum Preserving Recurrence cast le bk Rpow Coefficient
-- statement:
--   The potential estimate implies the explicit source linear-over-gap bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/QuantitativeRecurrence.lean#L394-L409
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/QuantitativeRecurrence.lean#L394-L409

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

theorem QEC.Locality.bkSumPreservingRecurrence_cast_le_bkRpowCoefficient
    (G : ConnectivityGraph ι) (d root parent : Nat) (beta c : ℝ)
    (hbeta : 0 ≤ beta) (hc0 : 0 ≤ c) (hc1 : c < 1) (hd : 2 ≤ d)
    (hparent : d ≤ parent) (hroot : parent ≤ root)
    (hprofile : ∀ scale : Nat, d ≤ scale → scale ≤ root →
      (twoThirdsSeparationProfile G scale : ℝ) ≤ beta * (scale : ℝ) ^ c) :
    (bkSumPreservingRecurrence G d parent : ℝ) ≤
      bkRpowCoefficient beta c * parent / (d : ℝ) ^ (1 - c) := by sorry
