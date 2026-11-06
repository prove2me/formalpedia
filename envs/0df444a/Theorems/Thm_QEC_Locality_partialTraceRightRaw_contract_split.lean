-- Prove2me | Theorems.Thm_QEC_Locality_partialTraceRightRaw_contract_split
-- name    : QEC.Locality.partialTraceRightRaw_contract_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:47:13.228834+00:00
-- url     : https://prove2.me/theorems/388404b7-cb0c-4e1c-91ed-6c21c5ecbed5
-- title:
--   Locality: partial Trace Right Raw contract split
-- statement:
--   The Locality construction uses the partial Trace Right Raw contract split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L80-L97
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L80-L97

import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Locality_CorrectableRegions_LocalPauliErasureTransfer
set_option autoImplicit false
open QEC QEC.Locality
open scoped TensorProduct BigOperators
open QEC Semantics
open Coding
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Locality.partialTraceRightRaw_contract_split (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K] :
    (contractLeft Complex H).comp
      ((TensorProduct.rid Complex (Module.Dual Complex H ⊗[Complex] H)).toLinearMap.comp
        ((TensorProduct.map
          (LinearMap.id : Module.Dual Complex H ⊗[Complex] H →ₗ[Complex]
            Module.Dual Complex H ⊗[Complex] H)
          (contractLeft Complex K)).comp
          (TensorProduct.tensorTensorTensorComm Complex
            (Module.Dual Complex H) (Module.Dual Complex K) H K).toLinearMap))
      =
    (contractLeft Complex (CompositeSystem H K)).comp
      (TensorProduct.congr (TensorProduct.dualDistribEquiv Complex H K)
        (LinearEquiv.refl Complex (CompositeSystem H K))).toLinearMap := by sorry
