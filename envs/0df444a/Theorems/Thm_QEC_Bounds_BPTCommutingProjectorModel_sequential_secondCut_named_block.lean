-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_sequential_secondCut_named_block
-- name    : QEC.Bounds.BPTCommutingProjectorModel.sequential_secondCut_named_block
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:34:38.973844+00:00
-- url     : https://prove2.me/theorems/c65ae9d4-b9c3-40b2-ac54-6fe9c1669de5
-- title:
--   BPTCommuting Projector Model: sequential second Cut named block
-- statement:
--   Named-interface adapter for `sequential_secondCut_block_of_intertwining`.
--   The three equality inputs keep concrete callers from unfolding large transport
--   and compression definitions while matching the generic theorem conclusion.
--   The right-factor naturality square is derived here from `UB` and `i`; concrete
--   callers must not restate that generic fact with a large model-specific type.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Sequential/SecondCutCore.lean#L105-L174
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Sequential/SecondCutCore.lean#L105-L174

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_BlockTransport
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sequential_SecondCutCore
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.sequential_secondCut_named_block
    {A H W N C C' X N2 D : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup C'] [InnerProductSpace Complex C'] [Semantics.FiniteQuantumSystem C']
    [NormedAddCommGroup X] [InnerProductSpace Complex X] [Semantics.FiniteQuantumSystem X]
    [NormedAddCommGroup N2] [InnerProductSpace Complex N2] [Semantics.FiniteQuantumSystem N2]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (UB : Semantics.UnitaryTransport H (Semantics.CompositeSystem W N))
    (UC : Semantics.UnitaryTransport C (Semantics.CompositeSystem X N2))
    (i : C →ₗ[Complex] C')
    (R : Semantics.Operator
      (Semantics.CompositeSystem (Semantics.CompositeSystem A H)
        (Semantics.CompositeSystem C' D)))
    (P : Semantics.Operator (Semantics.CompositeSystem A W))
    (Q : Semantics.Operator
      (Semantics.CompositeSystem N (Semantics.CompositeSystem C' D)))
    (Rsequential : Semantics.Operator
      (Semantics.CompositeSystem (Semantics.CompositeSystem A H)
        (Semantics.CompositeSystem C D)))
    (Qright : Semantics.Operator
      (Semantics.CompositeSystem N
        (Semantics.CompositeSystem X (Semantics.CompositeSystem N2 D))))
    (G : Semantics.UnitaryTransport
      (Semantics.CompositeSystem (Semantics.CompositeSystem A H)
        (Semantics.CompositeSystem C D))
      (Semantics.CompositeSystem (Semantics.CompositeSystem A W)
        (Semantics.CompositeSystem
          (Semantics.CompositeSystem N X) (Semantics.CompositeSystem N2 D))))
    (hRsequential :
      let K := TensorProduct.map (1 : Semantics.Operator (Semantics.CompositeSystem A H))
        (TensorProduct.map i (1 : Semantics.Operator D))
      Rsequential = (LinearMap.adjoint K).comp (R.comp K))
    (hQright :
      let Kright := TensorProduct.map (1 : Semantics.Operator N)
        (TensorProduct.map i (1 : Semantics.Operator D))
      let V := composeUnitaryTransport (unitaryRTensor UC D)
        (tensorAssociatorUnitary X N2 D)
      Qright = (unitaryLTensor N V).conjOperator
        ((LinearMap.adjoint Kright).comp (Q.comp Kright)))
    (hG :
      let V := composeUnitaryTransport (unitaryRTensor UC D)
        (tensorAssociatorUnitary X N2 D)
      G = composeUnitaryTransport
        (isotypicSectorBlockTransportLeft A H W N (Semantics.CompositeSystem C D) UB)
        (composeUnitaryTransport
          (unitaryLTensor (Semantics.CompositeSystem A W) (unitaryLTensor N V))
          (unitaryLTensor (Semantics.CompositeSystem A W)
            (tensorAssociatorUnitary N X (Semantics.CompositeSystem N2 D)).symm)))
    (hblock :
      (isotypicSectorBlockTransportLeft A H W N
        (Semantics.CompositeSystem C' D) UB).conjOperator R =
        TensorProduct.map P Q) :
    G.conjOperator Rsequential =
      (unitaryLTensor (Semantics.CompositeSystem A W)
        (tensorAssociatorUnitary N X (Semantics.CompositeSystem N2 D)).symm).conjOperator
        (TensorProduct.map P Qright) := by sorry
