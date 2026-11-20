-- Prove2me | Theorems.Thm_QEC_Bounds_registerFactorizedTensor_compression_left_of_embedding
-- name    : QEC.Bounds.registerFactorizedTensor_compression_left_of_embedding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:33:32.516725+00:00
-- url     : https://prove2.me/theorems/a65ffd20-3a8b-47f7-918c-f213d57ed61c
-- title:
--   Bounds: register Factorized Tensor compression left of embedding
-- statement:
--   The Bounds construction uses the register Factorized Tensor compression left of embedding property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Transport/SelectedTensorBridge.lean#L21-L37
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Transport/SelectedTensorBridge.lean#L21-L37

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_SelectedTensorCore
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_SelectedTensorBridge
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open scoped TensorProduct
universe u
set_option maxHeartbeats 150000
set_option synthInstance.maxHeartbeats 50000

theorem QEC.Bounds.registerFactorizedTensor_compression_left_of_embedding
    {iota : Type u} [Fintype iota] [DecidableEq iota] (q : iota → Nat)
    (S : Semantics.QuditSubsystem q)
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [Semantics.FiniteQuantumSystem K]
    (eSel : H →ₗ[Complex] S.selectedSystem) (eComp : K →ₗ[Complex] S.complementSystem)
    (J : Semantics.CompositeSystem H K →ₗ[Complex] S.factorizedSystem)
    (hJ : J = TensorProduct.map eSel eComp)
    (hComp : (LinearMap.adjoint eComp).comp eComp = (1 : Semantics.Operator K))
    (A : Semantics.Operator S.selectedSystem) :
    (LinearMap.adjoint J).comp
        ((S.registerFactorization.conjOperator (S.extendLocalToRegister A)).comp J) =
      TensorProduct.map ((LinearMap.adjoint eSel).comp (A.comp eSel))
        (1 : Semantics.Operator K) := by sorry
