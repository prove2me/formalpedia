-- Prove2me | Theorems.Thm_QEC_Locality_BKQLDPCFamily_recurrence_le_cMax_coefficient
-- name    : QEC.Locality.BKQLDPCFamily.recurrence_le_cMax_coefficient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:09:28.763205+00:00
-- url     : https://prove2.me/theorems/7baf2efe-6199-496d-a52f-2249777fbeef
-- title:
--   BKQLDPCFamily: recurrence le c Max coefficient
-- statement:
--   The attained measured exponent gives the exact finite one-pass BK estimate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/QuantitativeRecurrence.lean#L585-L602
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/QuantitativeRecurrence.lean#L585-L602

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

theorem QEC.Locality.BKQLDPCFamily.recurrence_le_cMax_coefficient
    (family : BKQLDPCFamily iota kappa) (i : family.Index) :
    (bkSumPreservingRecurrence (family.fixedGeneratorGraph i)
        (family.distance i.1) i.1 : ℝ) ≤
      bkRpowCoefficient 1 (family.cMax i) * i.1 /
        (family.distance i.1 : ℝ) ^ (1 - family.cMax i) := by sorry
