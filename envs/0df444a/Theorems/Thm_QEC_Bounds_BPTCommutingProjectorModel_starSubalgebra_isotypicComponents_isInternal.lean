-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_starSubalgebra_isotypicComponents_isInternal
-- name    : QEC.Bounds.BPTCommutingProjectorModel.starSubalgebra_isotypicComponents_isInternal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:24:40.783966+00:00
-- url     : https://prove2.me/theorems/5e30728c-b319-45b7-aa6f-3d80a1d46f1d
-- title:
--   BPTCommuting Projector Model: star Subalgebra isotypic Components is Internal
-- statement:
--   The isotypic components of a finite overlap interaction algebra form an
--   internal direct sum of the overlap module.  This is the direct-sum part of the
--   BV03 boundary decomposition; its index is representation-theoretic, not the
--   unrelated joint spectrum of the two global projectors.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L2850-L2859
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L2850-L2859

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

theorem QEC.Bounds.BPTCommutingProjectorModel.starSubalgebra_isotypicComponents_isInternal
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B)) :
    DirectSum.IsInternal (fun component : isotypicComponents S B => component.1) := by sorry
