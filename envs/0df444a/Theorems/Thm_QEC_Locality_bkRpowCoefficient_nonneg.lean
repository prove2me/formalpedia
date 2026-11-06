-- Prove2me | Theorems.Thm_QEC_Locality_bkRpowCoefficient_nonneg
-- name    : QEC.Locality.bkRpowCoefficient_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:37:40.721216+00:00
-- url     : https://prove2.me/theorems/d141bcba-7424-4e3a-ac49-c0d770405fba
-- title:
--   Locality: bk Rpow Coefficient nonneg
-- statement:
--   The Locality construction uses the bk Rpow Coefficient nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/QuantitativeRecurrence.lean#L201-L206
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/ConnectivityTradeoff/QuantitativeRecurrence.lean#L201-L206

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

theorem QEC.Locality.bkRpowCoefficient_nonneg
    {beta c : ℝ} (hbeta : 0 ≤ beta) (hc0 : 0 ≤ c) (hc1 : c < 1) :
    0 ≤ bkRpowCoefficient beta c := by sorry
