-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_regionErasureRecoverable_implies_noInformationOn
-- name    : QEC.Bounds.BPTCommutingProjectorModel.regionErasureRecoverable_implies_noInformationOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:51:15.604303+00:00
-- url     : https://prove2.me/theorems/eb717016-9416-4f79-95d5-ba6d181cff3a
-- title:
--   BPTCommuting Projector Model: region Erasure Recoverable implies no Information On
-- statement:
--   Concrete recovery from a BPT model region makes every local finite-qudit
--   effect information-free on the actual common-projector code.  This is the
--   recovery-to-no-information half of the finite-qudit bridge, specialized only
--   through the model's concrete region/subsystem bridge.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L48-L53
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L48-L53

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

theorem QEC.Bounds.BPTCommutingProjectorModel.regionErasureRecoverable_implies_noInformationOn
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (hcorrectable : M.RegionErasureRecoverable region) :
    Semantics.QuditSubsystem.NoInformationOn M.codeSpace (M.regionSubsystem region) := by sorry
