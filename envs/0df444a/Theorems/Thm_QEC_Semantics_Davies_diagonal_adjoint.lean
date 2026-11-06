-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_diagonal_adjoint
-- name    : QEC.Semantics.Davies.diagonal_adjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:27:19.144599+00:00
-- url     : https://prove2.me/theorems/32208b67-3193-41cc-b2ac-d88f13863476
-- title:
--   Davies: diagonal adjoint
-- statement:
--   The Davies construction uses the diagonal adjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Spectral.lean#L491-L498
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Spectral.lean#L491-L498

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

theorem QEC.Semantics.Davies.diagonal_adjoint (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ) :
    LinearMap.adjoint (diagonal b e) = diagonal b e := by sorry
