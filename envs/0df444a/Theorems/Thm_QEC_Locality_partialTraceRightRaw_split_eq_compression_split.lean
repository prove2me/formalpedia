-- Prove2me | Theorems.Thm_QEC_Locality_partialTraceRightRaw_split_eq_compression_split
-- name    : QEC.Locality.partialTraceRightRaw_split_eq_compression_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:38:27.207095+00:00
-- url     : https://prove2.me/theorems/7e79d6b4-0451-488f-9ddc-a814d0b0e944
-- title:
--   Locality: partial Trace Right Raw split eq compression split
-- statement:
--   The Locality construction uses the partial Trace Right Raw split eq compression split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L99-L121
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/CorrectableRegions/LocalPauliErasureTransfer.lean#L99-L121

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

theorem QEC.Locality.partialTraceRightRaw_split_eq_compression_split (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    {β : Type u} [Fintype β] (b : OrthonormalBasis β Complex K) :
    ((dualTensorHomEquiv Complex H H).toLinearMap.comp
      ((TensorProduct.rid Complex (Module.Dual Complex H ⊗[Complex] H)).toLinearMap.comp
        ((TensorProduct.map
          (LinearMap.id : Module.Dual Complex H ⊗[Complex] H →ₗ[Complex]
            Module.Dual Complex H ⊗[Complex] H)
          (contractLeft Complex K)).comp
          (TensorProduct.tensorTensorTensorComm Complex
            (Module.Dual Complex H) (Module.Dual Complex K) H K).toLinearMap)))
      =
    (rightCompression H K b).comp
      ((dualTensorHomEquiv Complex (CompositeSystem H K) (CompositeSystem H K)).toLinearMap.comp
        (TensorProduct.congr (TensorProduct.dualDistribEquiv Complex H K)
          (LinearEquiv.refl Complex (CompositeSystem H K))).toLinearMap) := by sorry
