-- Prove2me | Theorems.Thm_QEC_Locality_BKQLDPCFamily_recurrence_le_cMax_logarithmic_gap_bound
-- name    : QEC.Locality.BKQLDPCFamily.recurrence_le_cMax_logarithmic_gap_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:38:12.013539+00:00
-- url     : https://prove2.me/theorems/66d2e940-425d-4fa0-8eef-bb2e9b95a2a0
-- title:
--   BKQLDPCFamily: recurrence le c Max logarithmic gap bound
-- statement:
--   The actual measured `cMax` coefficient is logarithmic on an explicitly given
--   Lean-QEC `gamma`-gap.  The gap is an input condition on measured family data,
--   not a consequence of `cMax < 1`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/QuantitativeRecurrence.lean#L644-L670
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/QuantitativeRecurrence.lean#L644-L670

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

theorem QEC.Locality.BKQLDPCFamily.recurrence_le_cMax_logarithmic_gap_bound
    (family : BKQLDPCFamily iota kappa) (i : family.Index)
    {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : gamma ≤ (1 - family.cMax i) * Real.log i.1) :
    (bkSumPreservingRecurrence (family.fixedGeneratorGraph i)
        (family.distance i.1) i.1 : ℝ) ≤
      (3 * Real.log i.1 / (bkEntropyGap * gamma)) * i.1 /
        (family.distance i.1 : ℝ) ^ (1 - family.cMax i) := by sorry
