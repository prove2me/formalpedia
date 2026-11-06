-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_sequential_firstCut_named_block
-- name    : QEC.Bounds.BPTCommutingProjectorModel.sequential_firstCut_named_block
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:35:05.923099+00:00
-- url     : https://prove2.me/theorems/0ad54a63-17c8-4670-a640-566cf0ae50dc
-- title:
--   BPTCommuting Projector Model: sequential first Cut named block
-- statement:
--   Named-interface adapter for the concrete first-cut active block.  The caller
--   supplies definitional equalities for its named compression, left factor, and
--   transport; the generic naturality square remains internal to the core proof.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Sequential/FirstCutCore.lean#L99-L162
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Sequential/FirstCutCore.lean#L99-L162

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

theorem QEC.Bounds.BPTCommutingProjectorModel.sequential_firstCut_named_block
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
    (Rsequential : Semantics.Operator
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem (Semantics.CompositeSystem A B) H) D))
    (Pleft : Semantics.Operator
      (Semantics.CompositeSystem (Semantics.CompositeSystem A WB)
        (Semantics.CompositeSystem NB W)))
    (G : Semantics.UnitaryTransport
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem (Semantics.CompositeSystem A B) H) D)
      (Semantics.CompositeSystem
        (Semantics.CompositeSystem A WB)
        (Semantics.CompositeSystem (Semantics.CompositeSystem NB W)
          (Semantics.CompositeSystem N D))))
    (hRsequential :
      let K := TensorProduct.map
        (TensorProduct.map (TensorProduct.map (1 : Semantics.Operator A) i)
          (1 : Semantics.Operator H))
        (1 : Semantics.Operator D)
      Rsequential = (LinearMap.adjoint K).comp (R.comp K))
    (hPleft :
      let Kleft := TensorProduct.map (TensorProduct.map (1 : Semantics.Operator A) i)
        (1 : Semantics.Operator W)
      let TB := isotypicSectorBlockTransportLeft A B WB NB W UB
      Pleft = TB.conjOperator ((LinearMap.adjoint Kleft).comp (P.comp Kleft)))
    (hG :
      let TB := isotypicSectorBlockTransportLeft A B WB NB W UB
      G = composeUnitaryTransport
        (isotypicSectorBlockTransportLeft (Semantics.CompositeSystem A B) H W N D UC)
        (composeUnitaryTransport
          (unitaryRTensor TB (Semantics.CompositeSystem N D))
          (tensorAssociatorUnitary (Semantics.CompositeSystem A WB)
            (Semantics.CompositeSystem NB W) (Semantics.CompositeSystem N D))))
    (hblock :
      (isotypicSectorBlockTransportLeft (Semantics.CompositeSystem A B') H W N D UC).conjOperator R =
        TensorProduct.map P Q) :
    G.conjOperator Rsequential =
      (tensorAssociatorUnitary (Semantics.CompositeSystem A WB)
        (Semantics.CompositeSystem NB W) (Semantics.CompositeSystem N D)).conjOperator
        (TensorProduct.map Pleft Q) := by sorry
