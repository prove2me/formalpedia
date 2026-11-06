-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_sequential_firstCut_block_of_left_intertwining
-- name    : QEC.Bounds.BPTCommutingProjectorModel.sequential_firstCut_block_of_left_intertwining
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:34:29.647015+00:00
-- url     : https://prove2.me/theorems/c4845e38-6fef-4ee6-8db2-d32dbca1b6b7
-- title:
--   BPTCommuting Projector Model: sequential first Cut block of left intertwining
-- statement:
--   The first sequential compression of a BV03 block.  A left `B` subtype
--   embedding is carried through the first-cut isotypic `C` coordinates, then the
--   actual `B` coordinate change and the final source associator.  This is the
--   generic shape used to derive `hfirst` from the physical first-cut block.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Sequential/FirstCutCore.lean#L29-L92
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Sequential/FirstCutCore.lean#L29-L92

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_BlockTransport
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sequential_FirstCutCore
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.sequential_firstCut_block_of_left_intertwining
    {A B B' H W N D WB NB : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup B'] [InnerProductSpace Complex B'] [Semantics.FiniteQuantumSystem B']
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    [NormedAddCommGroup WB] [InnerProductSpace Complex WB] [Semantics.FiniteQuantumSystem WB]
    [NormedAddCommGroup NB] [InnerProductSpace Complex NB] [Semantics.FiniteQuantumSystem NB]
    (UC : Semantics.UnitaryTransport H (Semantics.CompositeSystem W N))
    (UB : Semantics.UnitaryTransport B (Semantics.CompositeSystem WB NB))
    (i : B →ₗ[Complex] B')
    (R : Semantics.Operator
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem (Semantics.CompositeSystem A B') H) D))
    (P : Semantics.Operator
      (Semantics.CompositeSystem (Semantics.CompositeSystem A B') W))
    (Q : Semantics.Operator (Semantics.CompositeSystem N D))
    (hblock :
      (isotypicSectorBlockTransportLeft (Semantics.CompositeSystem A B') H W N D UC).conjOperator R =
        TensorProduct.map P Q) :
    let K := TensorProduct.map
      (TensorProduct.map (TensorProduct.map (1 : Semantics.Operator A) i)
        (1 : Semantics.Operator H))
      (1 : Semantics.Operator D)
    let Kleft := TensorProduct.map (TensorProduct.map (1 : Semantics.Operator A) i)
      (1 : Semantics.Operator W)
    let TB := isotypicSectorBlockTransportLeft A B WB NB W UB
    let Pleft := TB.conjOperator ((LinearMap.adjoint Kleft).comp (P.comp Kleft))
    let G := composeUnitaryTransport
      (isotypicSectorBlockTransportLeft (Semantics.CompositeSystem A B) H W N D UC)
      (composeUnitaryTransport
        (unitaryRTensor TB (Semantics.CompositeSystem N D))
        (tensorAssociatorUnitary (Semantics.CompositeSystem A WB)
          (Semantics.CompositeSystem NB W) (Semantics.CompositeSystem N D)))
    G.conjOperator ((LinearMap.adjoint K).comp (R.comp K)) =
      (tensorAssociatorUnitary (Semantics.CompositeSystem A WB)
        (Semantics.CompositeSystem NB W) (Semantics.CompositeSystem N D)).conjOperator
        (TensorProduct.map Pleft Q) := by sorry
