-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_unitaryTransport_conj_compression_comp
-- name    : QEC.Bounds.BPTCommutingProjectorModel.unitaryTransport_conj_compression_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:27:11.966195+00:00
-- url     : https://prove2.me/theorems/ba49afb4-f77d-427c-9129-350f654c5969
-- title:
--   BPTCommuting Projector Model: unitary Transport conj compression comp
-- statement:
--   Conjugating an operator before compressing along the transported embedding is
--   exactly the original compression.  This is the algebraic core of the D5
--   comparison between a four-factor active block and its second-cut coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Regrouping.lean#L186-L203
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/Regrouping.lean#L186-L203

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_ActiveTransport
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Regrouping
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.unitaryTransport_conj_compression_comp
    {H K S : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    [NormedAddCommGroup S] [InnerProductSpace Complex S] [Semantics.FiniteQuantumSystem S]
    (T : Semantics.UnitaryTransport H K) (J : S →ₗ[Complex] H)
    (P : Semantics.Operator H) :
    (LinearMap.adjoint (T.toLinearEquiv.toLinearMap.comp J)).comp
        ((T.conjOperator P).comp (T.toLinearEquiv.toLinearMap.comp J)) =
      (LinearMap.adjoint J).comp (P.comp J) := by sorry
