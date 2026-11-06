-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_diagonal_symmetric
-- name    : QEC.Semantics.Davies.diagonal_symmetric
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:07:26.454759+00:00
-- url     : https://prove2.me/theorems/c2931a64-ba95-4a60-959c-40d50540be86
-- title:
--   Davies: diagonal symmetric
-- statement:
--   The Davies construction uses the diagonal symmetric property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Spectral.lean#L500-L502
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Spectral.lean#L500-L502

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

theorem QEC.Semantics.Davies.diagonal_symmetric (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ) :
    (diagonal b e).IsSymmetric := by sorry
