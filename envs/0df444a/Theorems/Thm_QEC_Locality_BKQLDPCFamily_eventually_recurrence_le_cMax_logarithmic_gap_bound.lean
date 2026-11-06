-- Prove2me | Theorems.Thm_QEC_Locality_BKQLDPCFamily_eventually_recurrence_le_cMax_logarithmic_gap_bound
-- name    : QEC.Locality.BKQLDPCFamily.eventually_recurrence_le_cMax_logarithmic_gap_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:28:41.587174+00:00
-- url     : https://prove2.me/theorems/eef92ee5-4946-48b5-918f-4dba49e3275f
-- title:
--   BKQLDPCFamily: eventually recurrence le c Max logarithmic gap bound
-- statement:
--   The logarithmic-gap recurrence estimate holds on the exact valid-index tail.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/QuantitativeRecurrence.lean#L692-L704
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/QuantitativeRecurrence.lean#L692-L704

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

theorem QEC.Locality.BKQLDPCFamily.eventually_recurrence_le_cMax_logarithmic_gap_bound
    (family : BKQLDPCFamily iota kappa) {gamma : ℝ} (hgamma : 0 < gamma)
    (hfamily : family.EventuallyOnValidIndices (fun i ↦
      gamma ≤ (1 - family.cMax i) * Real.log i.1)) :
    family.EventuallyOnValidIndices (fun i ↦
      (bkSumPreservingRecurrence (family.fixedGeneratorGraph i)
          (family.distance i.1) i.1 : ℝ) ≤
        (3 * Real.log i.1 / (bkEntropyGap * gamma)) * i.1 /
          (family.distance i.1 : ℝ) ^ (1 - family.cMax i)) := by sorry
