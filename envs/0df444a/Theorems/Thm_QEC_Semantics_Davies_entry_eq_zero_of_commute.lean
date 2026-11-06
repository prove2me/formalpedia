-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_entry_eq_zero_of_commute
-- name    : QEC.Semantics.Davies.entry_eq_zero_of_commute
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:58:08.048685+00:00
-- url     : https://prove2.me/theorems/17345eef-aa20-444d-a892-9c428ed40bcc
-- title:
--   Davies: entry eq zero of commute
-- statement:
--   The Davies construction uses the entry eq zero of commute property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Spectral.lean#L262-L268
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Spectral.lean#L262-L268

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

theorem QEC.Semantics.Davies.entry_eq_zero_of_commute (b : OrthonormalBasis ι ℂ V) (e : ι → ℝ)
    (A : Operator V) (hA : Commute (diagonal b e) A) (i j : ι)
    (hne : e i ≠ e j) : entry b A i j = 0 := by sorry
