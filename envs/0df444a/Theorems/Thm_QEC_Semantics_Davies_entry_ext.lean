-- Prove2me | Theorems.Thm_QEC_Semantics_Davies_entry_ext
-- name    : QEC.Semantics.Davies.entry_ext
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:55:38.777176+00:00
-- url     : https://prove2.me/theorems/47ad9646-2b0a-4ccc-a76c-4375d86d6d93
-- title:
--   Davies: entry ext
-- statement:
--   The Davies construction uses the entry ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Spectral.lean#L49-L55
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Dynamics/Davies/Spectral.lean#L49-L55

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

theorem QEC.Semantics.Davies.entry_ext (b : OrthonormalBasis ι ℂ V) {A B : Operator V}
    (h : ∀ i j, entry b A i j = entry b B i j) : A = B := by sorry
