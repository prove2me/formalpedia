-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteKrausFamily_mem_sameSpaceErrorSet_iff
-- name    : QEC.Semantics.FiniteKrausFamily.mem_sameSpaceErrorSet_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:18:14.718437+00:00
-- url     : https://prove2.me/theorems/d64f158c-eb88-4588-8b98-d1365dc6eee7
-- title:
--   Finite Kraus Family: mem same Space Error Set iff
-- statement:
--   The Finite Kraus Family construction uses the mem same Space Error Set iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/Kraus.lean#L378-L380
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/Kraus.lean#L378-L380

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

theorem QEC.Semantics.FiniteKrausFamily.mem_sameSpaceErrorSet_iff (E : FiniteKrausFamily ι H H) (F : Operator H) :
    F ∈ E.sameSpaceErrorSet ↔ ∃ i : ι, E.operator i = F := by sorry
