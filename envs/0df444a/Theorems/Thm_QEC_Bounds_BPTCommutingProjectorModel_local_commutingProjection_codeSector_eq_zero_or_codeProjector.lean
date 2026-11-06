-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_local_commutingProjection_codeSector_eq_zero_or_codeProjector
-- name    : QEC.Bounds.BPTCommutingProjectorModel.local_commutingProjection_codeSector_eq_zero_or_codeProjector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:20:11.774019+00:00
-- url     : https://prove2.me/theorems/dc1a89b4-b0b8-462c-a25f-697b8d12ce3f
-- title:
--   BPTCommuting Projector Model: local commuting Projection code Sector eq zero or code Projector
-- statement:
--   If a local projector `Z` commutes with the code projector, then its code
--   sector `Pi Z` is either zero or the whole code whenever the local subsystem
--   has no information.  Unlike a naive local-sector statement, the hypothesis is
--   locality of `Z` itself: `Pi Z` is generally global.  This is precisely the
--   source step that collapses the central BV03 boundary sectors after the first
--   and second interaction-algebra decompositions.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2548-L2600
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/FourFactor.lean#L2548-L2600

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

theorem QEC.Bounds.BPTCommutingProjectorModel.local_commutingProjection_codeSector_eq_zero_or_codeProjector
    (S : Semantics.QuditSubsystem L.localDimension) (C : Semantics.QuantumCode L.Register)
    {Z : Semantics.Operator L.Register}
    (hInformation : Semantics.QuditSubsystem.NoInformationOn C S)
    (hLocal : S.OperatorSupportedOnRegister Z)
    (hProjection : Z.IsSymmetricProjection)
    (hCommute : Commute C.projector Z) :
    C.projector * Z = 0 ∨ C.projector * Z = C.projector := by sorry
