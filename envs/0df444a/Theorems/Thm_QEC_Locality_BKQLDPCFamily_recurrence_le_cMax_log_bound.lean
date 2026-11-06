-- Prove2me | Theorems.Thm_QEC_Locality_BKQLDPCFamily_recurrence_le_cMax_log_bound
-- name    : QEC.Locality.BKQLDPCFamily.recurrence_le_cMax_log_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:37:51.030589+00:00
-- url     : https://prove2.me/theorems/f01ba6dc-f6f4-41d7-8e24-3e789494000f
-- title:
--   BKQLDPCFamily: recurrence le c Max log bound
-- statement:
--   The pointwise source threshold gives the explicit finite logarithmic coefficient.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/QuantitativeRecurrence.lean#L605-L637
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/QuantitativeRecurrence.lean#L605-L637

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
open QEC.Locality.BKQLDPCFamily
variable {iota : Nat → Type u} {kappa : Nat → Type v}
variable [∀ n, Fintype (iota n)] [∀ n, DecidableEq (iota n)]
variable [∀ n, Fintype (kappa n)]

theorem QEC.Locality.BKQLDPCFamily.recurrence_le_cMax_log_bound
    (family : BKQLDPCFamily iota kappa) (i : family.Index)
    (hthreshold : family.cMax i ≤
      1 + Real.logb (i.1 : ℝ) (1 / 3 : ℝ)) :
    (bkSumPreservingRecurrence (family.fixedGeneratorGraph i)
        (family.distance i.1) i.1 : ℝ) ≤
      (3 * Real.log i.1 / (bkEntropyGap * Real.log 3)) * i.1 /
        (family.distance i.1 : ℝ) ^ (1 - family.cMax i) := by sorry
