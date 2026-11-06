-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_diagonal_mul_projector
-- name    : QEC.Semantics.Davies.diagonal_mul_projector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:26:18.758321+00:00
-- url     : https://prove2.me/theorems/313c21e0-0324-44a8-80e2-4814fb09c816
-- title:
--   Davies: diagonal mul projector
-- statement:
--   The Davies construction uses the diagonal mul projector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Spectral.lean#L142-L153
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Spectral.lean#L142-L153

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

theorem QEC.Semantics.Davies.diagonal_mul_projector (b : OrthonormalBasis ι ℂ V)
    (energy : ι → ℝ) (E : ℝ) :
    diagonal b energy * energyProjector b energy E =
      (E : ℂ) • energyProjector b energy E := by sorry
