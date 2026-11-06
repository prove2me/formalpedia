-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_actualFrequency_add_commuting_remainder
-- name    : QEC.Semantics.Davies.actualFrequency_add_commuting_remainder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:13:27.722504+00:00
-- url     : https://prove2.me/theorems/dd3bc7a5-4ef0-4bfa-9731-efd93e629601
-- title:
--   Davies: actual Frequency add commuting remainder
-- statement:
--   Terms commuting with both the local Hamiltonian and coupling do not affect its frequencies.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/FrequencyLocality.lean#L90-L135
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/FrequencyLocality.lean#L90-L135

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

theorem QEC.Semantics.Davies.actualFrequency_add_commuting_remainder (L R A : Operator V)
    (hL : L.IsSymmetric) (hH : (L+R).IsSymmetric)
    (hLR : Commute L R) (hRA : Commute R A) (ω : ℝ) :
    actualFrequency (L+R) hH A ω = actualFrequency L hL A ω := by sorry
