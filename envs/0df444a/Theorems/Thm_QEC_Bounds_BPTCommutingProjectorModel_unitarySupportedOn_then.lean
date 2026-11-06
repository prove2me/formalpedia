-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_unitarySupportedOn_then
-- name    : QEC.Bounds.BPTCommutingProjectorModel.unitarySupportedOn_then
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:10:01.148795+00:00
-- url     : https://prove2.me/theorems/a8c77438-4dbc-4b6b-99bc-7506f5be8a59
-- title:
--   BPTCommuting Projector Model: unitary Supported On then
-- statement:
--   Support on a fixed region is closed under composition of unitary transports.
--   The local representatives compose in the same order as the global maps, so the
--   eventual BPT boundary unitary can be assembled from its two algebraic block
--   units and its final pure-state disentangler.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L218-L228
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L218-L228

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Data.Finset.NoncommProd
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.InnerProductSpace.Semisimple
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.unitarySupportedOn_then
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    {U V : Semantics.UnitaryTransport L.Register L.Register}
    (hU : M.UnitarySupportedOn region U) (hV : M.UnitarySupportedOn region V) :
    M.UnitarySupportedOn region (thenUnitary U V) := by sorry
