-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_sequential_secondCut_block_of_intertwining
-- name    : QEC.Bounds.BPTCommutingProjectorModel.sequential_secondCut_block_of_intertwining
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:34:30.112287+00:00
-- url     : https://prove2.me/theorems/b5129020-e4f4-40b3-b052-7096bec81881
-- title:
--   BPTCommuting Projector Model: sequential second Cut block of intertwining
-- statement:
--   The actual second sequential compression of a rank-one BV03 block.  A right
--   subtype embedding is transported through the first isotypic coordinate change,
--   then through the next isotypic unitary, yielding the literal `B'' tensor C'`
--   residual block.  The hypotheses are a source block equation and its concrete
--   intertwining square, not a preassembled sequential factorization.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Sequential/SecondCutCore.lean#L30-L96
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Sequential/SecondCutCore.lean#L30-L96

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

theorem QEC.Bounds.BPTCommutingProjectorModel.sequential_secondCut_block_of_intertwining
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
    (hblock :
      (isotypicSectorBlockTransportLeft A H W N
        (Semantics.CompositeSystem C' D) UB).conjOperator R =
        TensorProduct.map P Q)
    (hintertwines :
      (isotypicSectorBlockTransportLeft A H W N
        (Semantics.CompositeSystem C' D) UB).toLinearEquiv.toLinearMap.comp
          (TensorProduct.map (1 : Semantics.Operator (Semantics.CompositeSystem A H))
            (TensorProduct.map i (1 : Semantics.Operator D))) =
        (TensorProduct.map (1 : Semantics.Operator (Semantics.CompositeSystem A W))
          (TensorProduct.map (1 : Semantics.Operator N)
            (TensorProduct.map i (1 : Semantics.Operator D)))).comp
          (isotypicSectorBlockTransportLeft A H W N
            (Semantics.CompositeSystem C D) UB).toLinearEquiv.toLinearMap) :
    let K := TensorProduct.map (1 : Semantics.Operator (Semantics.CompositeSystem A H))
      (TensorProduct.map i (1 : Semantics.Operator D))
    let Kright := TensorProduct.map (1 : Semantics.Operator N)
      (TensorProduct.map i (1 : Semantics.Operator D))
    let V := composeUnitaryTransport (unitaryRTensor UC D)
      (tensorAssociatorUnitary X N2 D)
    let Qright := (unitaryLTensor N V).conjOperator
      ((LinearMap.adjoint Kright).comp (Q.comp Kright))
    let G := composeUnitaryTransport
      (isotypicSectorBlockTransportLeft A H W N (Semantics.CompositeSystem C D) UB)
      (composeUnitaryTransport
        (unitaryLTensor (Semantics.CompositeSystem A W) (unitaryLTensor N V))
        (unitaryLTensor (Semantics.CompositeSystem A W)
          (tensorAssociatorUnitary N X (Semantics.CompositeSystem N2 D)).symm))
    G.conjOperator ((LinearMap.adjoint K).comp (R.comp K)) =
      (unitaryLTensor (Semantics.CompositeSystem A W)
        (tensorAssociatorUnitary N X (Semantics.CompositeSystem N2 D)).symm).conjOperator
        (TensorProduct.map P Qright) := by sorry
