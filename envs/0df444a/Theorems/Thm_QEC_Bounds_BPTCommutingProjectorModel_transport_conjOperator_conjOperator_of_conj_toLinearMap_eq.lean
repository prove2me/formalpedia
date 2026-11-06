-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_transport_conjOperator_conjOperator_of_conj_toLinearMap_eq
-- name    : QEC.Bounds.BPTCommutingProjectorModel.transport_conjOperator_conjOperator_of_conj_toLinearMap_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:25:12.258112+00:00
-- url     : https://prove2.me/theorems/4b421d4c-eaf4-4b50-8ba0-60efcdac6802
-- title:
--   BPTCommuting Projector Model: transport conj Operator conj Operator of conj to Linear Map eq
-- statement:
--   If a transport carries an ambient unitary map to a second ambient unitary map,
--   then transporting a conjugated operator is conjugation of the transported
--   operator.  This is stated at the map level so it applies to the physical
--   boundary lift and its four-factor representative without any assertion about
--   the orthogonal complement of an active sector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/ActiveTransport.lean#L215-L242
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/Joint/ActiveTransport.lean#L215-L242

import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_Sector
import Definitions.Def_QEC_Bounds_BPTDisentangling_Joint_ActiveTransport
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.transport_conjOperator_conjOperator_of_conj_toLinearMap_eq
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (T : Semantics.UnitaryTransport H K) (U : Semantics.UnitaryTransport H H)
    (V : Semantics.UnitaryTransport K K)
    (htransport : T.conjOperator U.toLinearEquiv.toLinearMap =
      V.toLinearEquiv.toLinearMap)
    (P : Semantics.Operator H) :
    T.conjOperator (U.conjOperator P) = V.conjOperator (T.conjOperator P) := by sorry
