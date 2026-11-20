-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_finalAssembly_regrouping_intertwines
-- name    : QEC.Bounds.BPTCommutingProjectorModel.finalAssembly_regrouping_intertwines
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:14:51.685343+00:00
-- url     : https://prove2.me/theorems/afe76bb1-3097-444a-92af-cb0be111f90a
-- title:
--   BPTCommuting Projector Model: final Assembly regrouping intertwines
-- statement:
--   The final #388 regrouping carries the active `N tensor X` unitary entirely on
--   the left of the source split `((S tensor N) tensor X) tensor D`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SeparatedUnionBridge.lean#L257-L298
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/SeparatedUnionBridge.lean#L257-L298

import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_AssemblyTransport
import Definitions.Def_QEC_Bounds_BPTDisentangling_SeparatedUnionBridge
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open QEC.Bounds.BPTCommutingProjectorModel
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u

theorem QEC.Bounds.BPTCommutingProjectorModel.finalAssembly_regrouping_intertwines
    {A W N X D : Type u} [NormedAddCommGroup A] [InnerProductSpace Complex A]
    [Semantics.FiniteQuantumSystem A] [NormedAddCommGroup W] [InnerProductSpace Complex W]
    [Semantics.FiniteQuantumSystem W] [NormedAddCommGroup N] [InnerProductSpace Complex N]
    [Semantics.FiniteQuantumSystem N] [NormedAddCommGroup X] [InnerProductSpace Complex X]
    [Semantics.FiniteQuantumSystem X] [NormedAddCommGroup D] [InnerProductSpace Complex D]
    [Semantics.FiniteQuantumSystem D]
    (U : Semantics.UnitaryTransport (Semantics.CompositeSystem N X)
      (Semantics.CompositeSystem N X)) :
    let S := Semantics.CompositeSystem A W
    let regrouping := productBlockRegrouping (A := A) (W := W) (N := N) (X := X) (D := D)
    let commonAssociator := tensorAssociatorUnitary S (Semantics.CompositeSystem N X) D
    let commonCoordinates := composeUnitaryTransport regrouping.symm commonAssociator
    let commonUnitary := unitaryLTensor S (unitaryRTensor U D)
    let rawUnitary := conjugateUnitaryTransport commonCoordinates commonUnitary
    let outerAssociator := tensorAssociatorUnitary (Semantics.CompositeSystem S N) X D
    let leftUnitary := conjugateUnitaryTransport
      (tensorAssociatorUnitary S N X) (unitaryLTensor S U)
    rawUnitary.toLinearEquiv.toLinearMap.comp outerAssociator.toLinearEquiv.toLinearMap =
      outerAssociator.toLinearEquiv.toLinearMap.comp
        (unitaryRTensor leftUnitary D).toLinearEquiv.toLinearMap := by sorry
