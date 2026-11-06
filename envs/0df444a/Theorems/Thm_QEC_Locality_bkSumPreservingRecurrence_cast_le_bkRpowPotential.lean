-- Prove2me | Theorems.Thm_QEC_Locality_bkSumPreservingRecurrence_cast_le_bkRpowPotential
-- name    : QEC.Locality.bkSumPreservingRecurrence_cast_le_bkRpowPotential
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:37:56.027941+00:00
-- url     : https://prove2.me/theorems/3dd4ad13-fe2e-4abb-b07d-0be8453ac643
-- title:
--   Locality: bk Sum Preserving Recurrence cast le bk Rpow Potential
-- statement:
--   The source potential bounds the exact finite admissible-pair recurrence.
--   The profile hypothesis is required only on scales between the terminal
--   threshold and the chosen root.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/QuantitativeRecurrence.lean#L320-L391
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/QuantitativeRecurrence.lean#L320-L391

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

theorem QEC.Locality.bkSumPreservingRecurrence_cast_le_bkRpowPotential
    (G : ConnectivityGraph ι) (d root parent : Nat) (beta c : ℝ)
    (hbeta : 0 ≤ beta) (hc0 : 0 ≤ c) (hc1 : c < 1) (hd : 2 ≤ d)
    (hparent : d ≤ parent) (hroot : parent ≤ root)
    (hprofile : ∀ scale : Nat, d ≤ scale → scale ≤ root →
      (twoThirdsSeparationProfile G scale : ℝ) ≤ beta * (scale : ℝ) ^ c) :
    (bkSumPreservingRecurrence G d parent : ℝ) ≤
      bkRpowPotential beta c d parent := by sorry
