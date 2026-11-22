-- Prove2me | Theorems.Thm_P2M_Lean4LPD_LayerWitness_P__mem_reachable_unmerged_3e0878106649
-- name    : P2M_Lean4LPD_LayerWitness_P__mem_reachable_unmerged_3e0878106649
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T07:03:20.54094+00:00
-- url     : https://prove2.me/theorems/ef1ca04a-be44-45d8-bd2b-a3ec43b1fa39
-- title:
--   P2 M Lean4 LPD Layer Witness P  mem reachable unmerged 3e0878106649: P2 M Lean4 LPD Layer Witness P  mem reachable unmerged 3e0878106649
-- statement:
--   The literal `2Γ = 4` layer reading, obtained from the merged one by letting `P₆` sit out the
--   repeated `L₂`: deciding this directly would re-explore the whole four-layer branching tree.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerWitness.lean#L537-L540
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerWitness.lean#L537-L540

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Weight
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerWitness
set_option autoImplicit true
@[expose] public section
public section
open Lean4LPD
open Lean4LPD.LayerWitness
open PauliString

theorem P2M_Lean4LPD_LayerWitness_P__mem_reachable_unmerged_3e0878106649 : P₆ ∈ reachable (layers := [L₁, L₂, L₂, L₁]) (Z 3) := by sorry

alias «Lean4LPD».«LayerWitness».«P₆_mem_reachable_unmerged» := P2M_Lean4LPD_LayerWitness_P__mem_reachable_unmerged_3e0878106649
