-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_nestedFactorizationLeft_conj_extendLocalToRegister
-- name    : QEC.Bounds.BPTCommutingProjectorModel.nestedFactorizationLeft_conj_extendLocalToRegister
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:19:24.70804+00:00
-- url     : https://prove2.me/theorems/c33fc9ab-f042-4782-be4d-bc194611d95e
-- title:
--   BPTCommuting Projector Model: nested Factorization Left conj extend Local To Register
-- statement:
--   Conjugating an `S`-local identity extension through the left cumulative
--   factorization `S subset T` acts on `S` alone and is the identity on both
--   `T \\ S` and `T^c`.  This is the operator-level recombination identity used
--   to transport the three BPT source products into common coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L225-L244
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L225-L244

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.nestedFactorizationLeft_conj_extendLocalToRegister
    (S T : Semantics.QuditSubsystem L.localDimension) (hST : S.selected ⊆ T.selected)
    (A : Semantics.Operator S.selectedSystem) :
    (nestedFactorizationLeft S T hST).conjOperator (S.extendLocalToRegister A) =
      TensorProduct.map A
        (1 : Semantics.Operator
          (Semantics.CompositeSystem (S.additionalRetainedSystem T) T.complementSystem)) := by sorry
