-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_actualFrequency_add
-- name    : QEC.Semantics.Davies.actualFrequency_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:13:28.974003+00:00
-- url     : https://prove2.me/theorems/27c4ae41-404f-4d5f-982e-e0fe647c2291
-- title:
--   Davies: actual Frequency add
-- statement:
--   The Davies construction uses the actual Frequency add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/FrequencyLocality.lean#L143-L145
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/FrequencyLocality.lean#L143-L145

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

theorem QEC.Semantics.Davies.actualFrequency_add (H A B : Operator V) (hH : H.IsSymmetric) (ω : ℝ) :
    actualFrequency H hH (A+B) ω = actualFrequency H hH A ω + actualFrequency H hH B ω := by sorry
