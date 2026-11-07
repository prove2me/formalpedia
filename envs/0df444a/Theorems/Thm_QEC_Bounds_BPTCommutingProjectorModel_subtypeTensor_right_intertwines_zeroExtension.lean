-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_subtypeTensor_right_intertwines_zeroExtension
-- name    : QEC.Bounds.BPTCommutingProjectorModel.subtypeTensor_right_intertwines_zeroExtension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:58:44.315005+00:00
-- url     : https://prove2.me/theorems/a86e93d0-3d4c-475e-af53-19660f258e0b
-- title:
--   BPTCommuting Projector Model: subtype Tensor right intertwines zero Extension
-- statement:
--   Zero-extending a probe on an active subtype intertwines the subtype coordinates
--   with the physical coordinates.  This is the concrete lifting step used for
--   the external-boundary `C'` probes below.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/ScalarCompression/Core.lean#L86-L108
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/ScalarCompression/Core.lean#L86-L108

import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_Data
import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_Core
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 800000

theorem QEC.Bounds.BPTCommutingProjectorModel.subtypeTensor_right_intertwines_zeroExtension
    {N C D : Type u}
    [NormedAddCommGroup N] [InnerProductSpace Complex N]
    [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C]
    [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup D] [InnerProductSpace Complex D]
    [Semantics.FiniteQuantumSystem D]
    (p : Submodule Complex C) (E : Semantics.Operator p) :
    (TensorProduct.map (1 : Semantics.Operator N)
      (TensorProduct.map p.subtype (1 : Semantics.Operator D))).comp
      (TensorProduct.map (1 : Semantics.Operator N)
        (TensorProduct.map E (1 : Semantics.Operator D))) =
    (TensorProduct.map (1 : Semantics.Operator N)
      (TensorProduct.map (p.subtype.comp (E.comp (LinearMap.adjoint p.subtype)))
        (1 : Semantics.Operator D))).comp
      (TensorProduct.map (1 : Semantics.Operator N)
        (TensorProduct.map p.subtype (1 : Semantics.Operator D))) := by sorry
