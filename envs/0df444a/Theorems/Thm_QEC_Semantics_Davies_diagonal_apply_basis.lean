-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_diagonal_apply_basis
-- name    : QEC.Semantics.Davies.diagonal_apply_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:03:55.000092+00:00
-- url     : https://prove2.me/theorems/9729aca4-465b-4dda-bc50-013d0282659b
-- title:
--   Davies: diagonal apply basis
-- statement:
--   The Davies construction uses the diagonal apply basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Spectral.lean#L364-L367
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Spectral.lean#L364-L367

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

theorem QEC.Semantics.Davies.diagonal_apply_basis (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ) (i : ι) :
    diagonal b e (b i) = (e i : ℂ) • b i := by sorry
