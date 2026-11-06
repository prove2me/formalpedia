-- Prove2me | Theorems.Thm_QEC_Locality_bkSumPreservingRecurrence_le_coefficient_mul_scale_mul_depth
-- name    : QEC.Locality.bkSumPreservingRecurrence_le_coefficient_mul_scale_mul_depth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:36:59.494462+00:00
-- url     : https://prove2.me/theorems/c12e70fb-63a2-40a8-ad1a-b3c3944628fa
-- title:
--   Locality: bk Sum Preserving Recurrence le coefficient mul scale mul depth
-- statement:
--   Any scale-linear separator charge yields an explicit finite
--   `coefficient * parent * two-thirds-depth` recurrence bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/SumPreservingRecurrence.lean#L321-L393
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/SumPreservingRecurrence.lean#L321-L393

import Definitions.Def_QEC_Locality_ConnectivityTradeoff_RecursiveSeparator
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_MaxFamily
import Definitions.Def_QEC_Locality_ConnectivityTradeoff_SumPreservingRecurrence
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.bkSumPreservingRecurrence_le_coefficient_mul_scale_mul_depth
    (G : ConnectivityGraph ι) (d coefficient parent : Nat)
    (hprofile : ∀ scale : Nat, d ≤ scale →
      twoThirdsSeparationProfile G scale ≤ coefficient * scale) :
    bkSumPreservingRecurrence G d parent ≤
      coefficient * parent * bkTwoThirdsDepth d parent := by sorry
