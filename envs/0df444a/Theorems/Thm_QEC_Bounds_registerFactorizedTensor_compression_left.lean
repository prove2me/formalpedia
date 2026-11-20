-- Prove2me | Theorems.Thm_QEC_Bounds_registerFactorizedTensor_compression_left
-- name    : QEC.Bounds.registerFactorizedTensor_compression_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:29:39.44641+00:00
-- url     : https://prove2.me/theorems/4395982b-eb16-4c2c-8815-3e6a651ccc13
-- title:
--   Bounds: register Factorized Tensor compression left
-- statement:
--   After factoring a qudit register, a local selected action compressed through a
--   pair of embeddings acts trivially on the complement coordinate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Transport/SelectedTensorCore.lean#L25-L40
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTSeparatedUnion/Transport/SelectedTensorCore.lean#L25-L40

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_Coordinates
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_SelectedTensorCore
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open scoped TensorProduct
universe u v
set_option maxHeartbeats 150000
set_option synthInstance.maxHeartbeats 50000

theorem QEC.Bounds.registerFactorizedTensor_compression_left
    {iota : Type u} [Fintype iota] [DecidableEq iota] (q : iota → Nat)
    (S : Semantics.QuditSubsystem q)
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [Semantics.FiniteQuantumSystem K]
    (eSel : H →ₗ[Complex] S.selectedSystem) (eComp : K →ₗ[Complex] S.complementSystem)
    (hComp : (LinearMap.adjoint eComp).comp eComp = (1 : Semantics.Operator K))
    (A : Semantics.Operator S.selectedSystem) :
    (LinearMap.adjoint (TensorProduct.map eSel eComp)).comp
        ((S.registerFactorization.conjOperator (S.extendLocalToRegister A)).comp
          (TensorProduct.map eSel eComp)) =
      TensorProduct.map ((LinearMap.adjoint eSel).comp (A.comp eSel))
        (1 : Semantics.Operator K) := by sorry
