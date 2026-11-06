-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_extendSubmoduleUnitary_apply_subtype
-- name    : QEC.Bounds.BPTCommutingProjectorModel.extendSubmoduleUnitary_apply_subtype
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:22:35.408199+00:00
-- url     : https://prove2.me/theorems/e3684585-b935-46e4-8025-0506bededafa
-- title:
--   BPTCommuting Projector Model: extend Submodule Unitary apply subtype
-- statement:
--   The ambient extension agrees with the prescribed unitary on its submodule.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L414-L429
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L414-L429

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

theorem QEC.Bounds.BPTCommutingProjectorModel.extendSubmoduleUnitary_apply_subtype
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] (S : Submodule Complex H)
    (U : Semantics.UnitaryTransport S S) (s : S) :
    extendSubmoduleUnitary S U (s : H) = (U s : S) := by sorry
