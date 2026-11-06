-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_actualFrequency_energyDifference
-- name    : QEC.Semantics.Davies.actualFrequency_energyDifference
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:29:49.094571+00:00
-- url     : https://prove2.me/theorems/e18a7ecf-dcd1-4797-ace7-94f421b93fad
-- title:
--   Davies: actual Frequency energy Difference
-- statement:
--   The Davies construction uses the actual Frequency energy Difference property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/FrequencyLocality.lean#L74-L87
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/FrequencyLocality.lean#L74-L87

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

theorem QEC.Semantics.Davies.actualFrequency_energyDifference (H : Operator V) (hH : H.IsSymmetric)
    (A : Operator V) (ω : ℝ) :
    energyDifference H (actualFrequency H hH A ω) = (ω : ℂ) • actualFrequency H hH A ω := by sorry
