-- Prove2me | Theorems.Thm_QEC_Locality_BKQLDPCFamily_eventually_recurrence_le_uniform_ceiling
-- name    : QEC.Locality.BKQLDPCFamily.eventually_recurrence_le_uniform_ceiling
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:28:43.948928+00:00
-- url     : https://prove2.me/theorems/b5bb5197-c191-47c7-9281-1ad41cec484e
-- title:
--   BKQLDPCFamily: eventually recurrence le uniform ceiling
-- statement:
--   `UniformCMaxBelowOne` supplies one constant and one valid-index tail.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/QuantitativeRecurrence.lean#L761-L774
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/QuantitativeRecurrence.lean#L761-L774

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

theorem QEC.Locality.BKQLDPCFamily.eventually_recurrence_le_uniform_ceiling
    (family : BKQLDPCFamily iota kappa)
    (hfamily : family.UniformCMaxBelowOne) :
    ∃ ceiling : ℝ, 0 < ceiling ∧ ceiling < 1 ∧
      family.EventuallyOnValidIndices (fun i ↦
        (bkSumPreservingRecurrence (family.fixedGeneratorGraph i)
            (family.distance i.1) i.1 : ℝ) ≤
          (3 / (bkEntropyGap * (1 - ceiling))) * i.1 /
            (family.distance i.1 : ℝ) ^ (1 - family.cMax i)) := by sorry
