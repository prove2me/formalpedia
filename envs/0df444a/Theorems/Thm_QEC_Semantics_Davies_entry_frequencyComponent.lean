-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_entry_frequencyComponent
-- name    : QEC.Semantics.Davies.entry_frequencyComponent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:54:47.291473+00:00
-- url     : https://prove2.me/theorems/36fd9a82-bdeb-4e04-8aa5-d3c39aac6ebd
-- title:
--   Davies: entry frequency Component
-- statement:
--   The Davies construction uses the entry frequency Component property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Spectral.lean#L181-L195
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Spectral.lean#L181-L195

import Definitions.Def_QEC_Semantics_Dynamics_ThermalEncoding
import Definitions.Def_QEC_Semantics_Dynamics_FourBlockGenerator
import Definitions.Def_QEC_Semantics_Dynamics_Davies_Spectral
set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.Davies
open Classical
open scoped BigOperators
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem QEC.Semantics.Davies.entry_frequencyComponent (b : OrthonormalBasis ι ℂ V) (energy : ι → ℝ)
    (A : Operator V) (ω : ℝ) (i j : ι) :
    entry b (frequencyComponent b energy A ω) i j =
      if energy j - energy i = ω then entry b A i j else 0 := by sorry
