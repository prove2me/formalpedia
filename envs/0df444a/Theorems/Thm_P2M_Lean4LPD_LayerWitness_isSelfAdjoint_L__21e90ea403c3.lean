-- Prove2me | Theorems.Thm_P2M_Lean4LPD_LayerWitness_isSelfAdjoint_L__21e90ea403c3
-- name    : P2M_Lean4LPD_LayerWitness_isSelfAdjoint_L__21e90ea403c3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:02:59.216805+00:00
-- url     : https://prove2.me/theorems/2088b517-86cf-479a-9cef-93f49a8f00c7
-- title:
--   P2 M Lean4 LPD Layer Witness is Self Adjoint L  21e90ea403c3: P2 M Lean4 LPD Layer Witness is Self Adjoint L  21e90ea403c3
-- statement:
--   Every generator used is a Hermitian Pauli string, so each layer really is a product of Pauli
--   rotations `e^{-iθG}` with `G† = G` and `G² = 1` (`isSelfAdjoint_iff_mul_self_eq_one`). None of them
--   has a `Y` site, so phase `0` is the Hermitian representative.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerWitness.lean#L469-L471
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerWitness.lean#L469-L471

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.LayerWitness
open PauliString

theorem P2M_Lean4LPD_LayerWitness_isSelfAdjoint_L__21e90ea403c3 : ∀ G ∈ L₁, IsSelfAdjoint G := by sorry

alias «Lean4LPD».«LayerWitness».«isSelfAdjoint_L₁» := P2M_Lean4LPD_LayerWitness_isSelfAdjoint_L__21e90ea403c3
