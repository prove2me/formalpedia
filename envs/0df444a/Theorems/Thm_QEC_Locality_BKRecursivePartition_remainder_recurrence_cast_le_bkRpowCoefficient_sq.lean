-- Prove2me | Theorems.Thm_QEC_Locality_BKRecursivePartition_remainder_recurrence_cast_le_bkRpowCoefficient_sq
-- name    : QEC.Locality.BKRecursivePartition.remainder_recurrence_cast_le_bkRpowCoefficient_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:27:48.332834+00:00
-- url     : https://prove2.me/theorems/eefb0cb4-3dff-4eef-9c8d-c1623fe346db
-- title:
--   BKRecursive Partition: remainder recurrence cast le bk Rpow Coefficient sq
-- statement:
--   Applying the concrete #380 partition a second time costs at most the square of
--   the one-pass coefficient.  The second recurrence is evaluated at the actual
--   first remainder cardinality, not at an independently maximized child scale.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/QuantitativeRecurrence.lean#L509-L576
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/QuantitativeRecurrence.lean#L509-L576

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

theorem QEC.Locality.BKRecursivePartition.remainder_recurrence_cast_le_bkRpowCoefficient_sq
    {G : ConnectivityGraph ι} {d : Nat} {vertices : Finset ι}
    (partition : BKRecursivePartition G d vertices) (beta c : ℝ)
    (hbeta : 0 ≤ beta) (hc0 : 0 ≤ c) (hc1 : c < 1) (hd : 2 ≤ d)
    (hvertices : d ≤ vertices.card)
    (hprofile : ∀ scale : Nat, d ≤ scale → scale ≤ vertices.card →
      (twoThirdsSeparationProfile G scale : ℝ) ≤ beta * (scale : ℝ) ^ c) :
    (bkSeparatorRecurrence G d partition.remainder : ℝ) ≤
      (bkRpowCoefficient beta c * bkRpowCoefficient beta c) * vertices.card /
        (((d : ℝ) ^ (1 - c)) * ((d : ℝ) ^ (1 - c))) := by sorry
