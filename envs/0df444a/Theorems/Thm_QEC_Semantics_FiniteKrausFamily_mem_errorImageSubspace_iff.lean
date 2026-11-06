-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteKrausFamily_mem_errorImageSubspace_iff
-- name    : QEC.Semantics.FiniteKrausFamily.mem_errorImageSubspace_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:11:39.103418+00:00
-- url     : https://prove2.me/theorems/2e91f01d-4c35-4b9e-a717-f608a843b95a
-- title:
--   Finite Kraus Family: mem error Image Subspace iff
-- statement:
--   The Finite Kraus Family construction uses the mem error Image Subspace iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/KrausKnillLaflamme.lean#L48-L52
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/KrausKnillLaflamme.lean#L48-L52

import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_KnillLaflamme
import Definitions.Def_QEC_Semantics_Channels_KrausKnillLaflamme
set_option autoImplicit false
universe u v
open QEC
open QEC.Semantics
noncomputable section
open QEC.Semantics.FiniteKrausFamily
variable {ι : Type v} [Fintype ι]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]

theorem QEC.Semantics.FiniteKrausFamily.mem_errorImageSubspace_iff
    (E : FiniteKrausFamily ι H H) (C : QuantumCode H) (i : ι) (x : H) :
    x ∈ E.errorImageSubspace C i ↔
      ∃ y : H, y ∈ C.carrier ∧ E.operator i y = x := by sorry
