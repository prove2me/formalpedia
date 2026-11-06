-- Prove2me | Theorems.Thm_QEC_Semantics_trace_projection_add_complement
-- name    : QEC.Semantics.trace_projection_add_complement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:25:41.737972+00:00
-- url     : https://prove2.me/theorems/a08fffcb-b133-4123-ad77-01196b2724c0
-- title:
--   Semantics: trace projection add complement
-- statement:
--   The Semantics construction uses the trace projection add complement property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/OperatorTraceNorm.lean#L469-L474
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/OperatorTraceNorm.lean#L469-L474

import Definitions.Def_QEC_Semantics_Core_Definitions
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Definitions.Def_QEC_Semantics_Core_OperatorTraceNorm
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]

theorem QEC.Semantics.trace_projection_add_complement (P A : Operator H) :
    LinearMap.trace Complex H (P * A) +
      LinearMap.trace Complex H ((1 - P) * A) =
        LinearMap.trace Complex H A := by sorry
