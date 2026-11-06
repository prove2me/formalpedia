-- Prove2me | Theorems.Thm_QEC_Locality_BKQLDPCFamily_recurrence_le_uniform_ceiling
-- name    : QEC.Locality.BKQLDPCFamily.recurrence_le_uniform_ceiling
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:37:59.814619+00:00
-- url     : https://prove2.me/theorems/0d1ee030-1bd4-4152-a14d-6e6349030740
-- title:
--   BKQLDPCFamily: recurrence le uniform ceiling
-- statement:
--   A fixed exponent ceiling below one uniformly controls the coefficient while
--   preserving the sharper pointwise `cMax` exponent in the distance denominator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/QuantitativeRecurrence.lean#L710-L758
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/QuantitativeRecurrence.lean#L710-L758

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

theorem QEC.Locality.BKQLDPCFamily.recurrence_le_uniform_ceiling
    (family : BKQLDPCFamily iota kappa) (i : family.Index)
    {ceiling : ℝ} (_hceiling0 : 0 ≤ ceiling) (hceiling1 : ceiling < 1)
    (hcMax : family.cMax i ≤ ceiling) :
    (bkSumPreservingRecurrence (family.fixedGeneratorGraph i)
        (family.distance i.1) i.1 : ℝ) ≤
      (3 / (bkEntropyGap * (1 - ceiling))) * i.1 /
        (family.distance i.1 : ℝ) ^ (1 - family.cMax i) := by sorry
