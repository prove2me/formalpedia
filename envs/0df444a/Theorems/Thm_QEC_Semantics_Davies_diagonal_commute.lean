-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_diagonal_commute
-- name    : QEC.Semantics.Davies.diagonal_commute
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:28:32.420314+00:00
-- url     : https://prove2.me/theorems/7de50f47-cce4-4ddc-acfd-d270257ad981
-- title:
--   Davies: diagonal commute
-- statement:
--   The Davies construction uses the diagonal commute property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Stationarity.lean#L46-L54
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Stationarity.lean#L46-L54

import Definitions.Def_QEC_Semantics_Dynamics_Davies_Spectral
import Definitions.Def_QEC_Semantics_Dynamics_Davies_Stationarity
set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.Davies
open Classical ThermalEncoding
open scoped BigOperators
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteQuantumSystem V]
variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem QEC.Semantics.Davies.diagonal_commute (b : OrthonormalBasis ι ℂ V) (e f : ι → ℝ) :
    Commute (diagonal b e) (diagonal b f) := by sorry
