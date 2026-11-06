-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_sequential_isotypicSectorBlockTransportLeft_coherence
-- name    : QEC.Bounds.BPTCommutingProjectorModel.sequential_isotypicSectorBlockTransportLeft_coherence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T15:10:57.41113+00:00
-- url     : https://prove2.me/theorems/07f0a043-cf7b-4fa0-a689-2be17397bebc
-- title:
--   BPTCommuting Projector Model: sequential isotypic Sector Block Transport Left coherence
-- statement:
--   The two sequential sector coordinate systems are coherent after the literal
--   source reassociation from `((A B) C) D` to `(A B) (C D)`.  This is the
--   concrete `htransport` used by the BPT common-factor argument.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Sequential/Coherence.lean#L66-L195
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Sequential/Coherence.lean#L66-L195

import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Transport
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sequential_Coherence
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

theorem QEC.Bounds.BPTCommutingProjectorModel.sequential_isotypicSectorBlockTransportLeft_coherence
    {A H W N C X N2 D : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    [NormedAddCommGroup X] [InnerProductSpace Complex X] [Semantics.FiniteQuantumSystem X]
    [NormedAddCommGroup N2] [InnerProductSpace Complex N2] [Semantics.FiniteQuantumSystem N2]
    [NormedAddCommGroup D] [InnerProductSpace Complex D] [Semantics.FiniteQuantumSystem D]
    (UB : Semantics.UnitaryTransport H (Semantics.CompositeSystem W N))
    (UC : Semantics.UnitaryTransport C (Semantics.CompositeSystem X N2)) :
    composeUnitaryTransport
        (tensorAssociatorUnitary (Semantics.CompositeSystem A H) C D)
        (composeUnitaryTransport
          (isotypicSectorBlockTransportLeft A H W N
            (Semantics.CompositeSystem C D) UB)
          (composeUnitaryTransport
            (unitaryLTensor (Semantics.CompositeSystem A W)
              (unitaryLTensor N
                (composeUnitaryTransport (unitaryRTensor UC D)
                  (tensorAssociatorUnitary X N2 D))))
            (unitaryLTensor (Semantics.CompositeSystem A W)
              (tensorAssociatorUnitary N X (Semantics.CompositeSystem N2 D)).symm))) =
      composeUnitaryTransport
        (isotypicSectorBlockTransportLeft (Semantics.CompositeSystem A H) C X N2 D UC)
        (composeUnitaryTransport
          (unitaryRTensor (isotypicSectorBlockTransportLeft A H W N X UB)
            (Semantics.CompositeSystem N2 D))
          (tensorAssociatorUnitary (Semantics.CompositeSystem A W)
            (Semantics.CompositeSystem N X) (Semantics.CompositeSystem N2 D))) := by sorry
