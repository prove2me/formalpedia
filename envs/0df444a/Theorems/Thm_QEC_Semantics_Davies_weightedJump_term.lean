-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_weightedJump_term
-- name    : QEC.Semantics.Davies.weightedJump_term
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:05:18.586133+00:00
-- url     : https://prove2.me/theorems/c563077a-5e25-4119-9d5d-15800ef07e8e
-- title:
--   Davies: weighted Jump term
-- statement:
--   The Davies construction uses the weighted Jump term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Stationarity.lean#L75-L83
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Stationarity.lean#L75-L83

import Definitions.Def_QEC_Semantics_Dynamics_Davies_Spectral
import Definitions.Def_QEC_Semantics_Dynamics_Davies_Stationarity
set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.Davies
open Classical ThermalEncoding
open scoped BigOperators
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V]
variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem QEC.Semantics.Davies.weightedJump_term {κ : Type*} (b : OrthonormalBasis ι ℂ V)
    (e : ι → ℝ) (A : κ → Operator V) (rate : κ → Frequency e → ℝ)
    (hn : ∀ a w, 0 ≤ rate a w) (a : κ × Frequency e) (F : Operator V) :
    lindbladJumpTerm (weightedJump b e A rate a) F =
      (rate a.1 a.2 : ℂ) • lindbladJumpTerm (frequencyComponent b e (A a.1) a.2.val) F := by sorry
