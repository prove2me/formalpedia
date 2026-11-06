-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteKrausFamily_complete_of_inducedMap_trace_preserving
-- name    : QEC.Semantics.FiniteKrausFamily.complete_of_inducedMap_trace_preserving
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:18:46.747189+00:00
-- url     : https://prove2.me/theorems/dc87c269-b634-4edb-9498-02e742a8a68d
-- title:
--   Finite Kraus Family: complete of induced Map trace preserving
-- statement:
--   Trace preservation of the induced operator-sum map forces Kraus completeness.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/Kraus.lean#L246-L260
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/Kraus.lean#L246-L260

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

theorem QEC.Semantics.FiniteKrausFamily.complete_of_inducedMap_trace_preserving (E : FiniteKrausFamily ι H K)
    (htrace : ∀ A : Operator H,
      LinearMap.trace Complex K (E.inducedMap A) = LinearMap.trace Complex H A) :
    E.Complete := by sorry
