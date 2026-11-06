-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_frequencyComponent_smul
-- name    : QEC.Semantics.Davies.frequencyComponent_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:12:24.378138+00:00
-- url     : https://prove2.me/theorems/ab7cb00b-991b-4be2-a99a-34ad9d4ccf99
-- title:
--   Davies: frequency Component smul
-- statement:
--   The Davies construction uses the frequency Component smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/FrequencyLocality.lean#L25-L31
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/FrequencyLocality.lean#L25-L31

import Definitions.Def_QEC_Semantics_Dynamics_Davies_Hamiltonian
import Definitions.Def_QEC_Semantics_Core_SubsystemOperatorAlgebra
import Definitions.Def_QEC_Semantics_Dynamics_Davies_FrequencyLocality
set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.Davies
open Classical
open scoped BigOperators
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem QEC.Semantics.Davies.frequencyComponent_smul (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ)
    (c : ℂ) (A : Operator V) (ω : ℝ) :
    frequencyComponent b e (c • A) ω = c • frequencyComponent b e A ω := by sorry
