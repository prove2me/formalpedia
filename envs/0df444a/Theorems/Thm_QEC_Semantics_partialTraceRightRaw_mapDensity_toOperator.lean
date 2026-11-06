-- Prove2me | Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
-- name    : QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:47:30.017255+00:00
-- url     : https://prove2.me/theorems/b7dabad3-6afe-4f8d-8e83-1dbef3954195
-- title:
--   Semantics: partial Trace Right Raw map Density to Operator
-- statement:
--   The Semantics construction uses the partial Trace Right Raw map Density to Operator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/Core.lean#L332-L338
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/Core.lean#L332-L338

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Channels_Core
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped TensorProduct

theorem QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (rho : DensityOperator (CompositeSystem H K)) :
    (partialTraceRightRaw_mapDensity H K rho).toOperator =
      (partialTraceRightRaw H K) rho.toOperator := by sorry

attribute [defeq] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator
