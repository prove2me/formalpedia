-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_sum_energyProjector
-- name    : QEC.Semantics.Davies.sum_energyProjector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:26:10.49657+00:00
-- url     : https://prove2.me/theorems/0fb021f5-8de2-489b-a9d3-79bf2be8c76e
-- title:
--   Davies: sum energy Projector
-- statement:
--   The Davies construction uses the sum energy Projector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Spectral.lean#L133-L140
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Spectral.lean#L133-L140

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

theorem QEC.Semantics.Davies.sum_energyProjector (b : OrthonormalBasis ι ℂ V) (energy : ι → ℝ) :
    (∑ E ∈ energyValues energy, energyProjector b energy E) = 1 := by sorry
