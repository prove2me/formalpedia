-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_actualFrequency_of_eigenoperator
-- name    : QEC.Semantics.Davies.actualFrequency_of_eigenoperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:30:49.522471+00:00
-- url     : https://prove2.me/theorems/c8f0fcc1-8ddf-469d-97b0-0241330b3cbd
-- title:
--   Davies: actual Frequency of eigenoperator
-- statement:
--   The Davies construction uses the actual Frequency of eigenoperator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/FrequencyLocality.lean#L137-L141
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/FrequencyLocality.lean#L137-L141

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

theorem QEC.Semantics.Davies.actualFrequency_of_eigenoperator (H A : Operator V) (hH : H.IsSymmetric)
    (freq ω : ℝ) (hA : energyDifference H A = (freq : ℂ) • A) :
    actualFrequency H hH A ω = if freq=ω then A else 0 := by sorry
