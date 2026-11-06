-- Prove2me | Theorems.Thm_QEC_Semantics_PartialTraceRight_map_positive_operator
-- name    : QEC.Semantics.PartialTraceRight.map_positive_operator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:36:16.594447+00:00
-- url     : https://prove2.me/theorems/cda2fca8-809e-44f7-b6c7-96e298256b6c
-- title:
--   Partial Trace Right: map positive operator
-- statement:
--   The Partial Trace Right construction uses the map positive operator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Definitions.lean#L618-L620
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Definitions.lean#L618-L620

import Mathlib
import Definitions.Def_QEC_Semantics_Core_Definitions
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped TensorProduct ComplexOrder
open QEC.Semantics.PartialTraceRight
variable {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K]

theorem QEC.Semantics.PartialTraceRight.map_positive_operator (tr : PartialTraceRight H K) {A : Operator (CompositeSystem H K)}
    (hA : LinearMap.IsPositive A) : LinearMap.IsPositive (tr A) := by sorry
