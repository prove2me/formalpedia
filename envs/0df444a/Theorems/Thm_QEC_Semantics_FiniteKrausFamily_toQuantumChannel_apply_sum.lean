-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteKrausFamily_toQuantumChannel_apply_sum
-- name    : QEC.Semantics.FiniteKrausFamily.toQuantumChannel_apply_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:17:50.792223+00:00
-- url     : https://prove2.me/theorems/fb261b5e-29a9-4664-9c01-ded200d87647
-- title:
--   Finite Kraus Family: to Quantum Channel apply sum
-- statement:
--   The Finite Kraus Family construction uses the to Quantum Channel apply sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/Kraus.lean#L280-L284
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/Kraus.lean#L280-L284

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Channels_Kraus
set_option autoImplicit false
universe u v
open QEC
open QEC.Semantics
open scoped BigOperators
noncomputable section
open QEC.Semantics.FiniteKrausFamily
variable {ι : Type v} [Fintype ι]
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]

theorem QEC.Semantics.FiniteKrausFamily.toQuantumChannel_apply_sum (E : FiniteKrausFamily ι H K) (hE : E.Complete)
    (A : Operator H) :
    (E.toQuantumChannel hE) A =
      ∑ i : ι, (E.operator i).comp (A.comp (LinearMap.adjoint (E.operator i))) := by sorry
