-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_starProjection_commute_starSubalgebraSubmodule
-- name    : QEC.Bounds.BPTCommutingProjectorModel.starProjection_commute_starSubalgebraSubmodule
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:24:34.524031+00:00
-- url     : https://prove2.me/theorems/2fe119c9-6b9f-479f-a33f-a3e64694b9fb
-- title:
--   BPTCommuting Projector Model: star Projection commute star Subalgebra Submodule
-- statement:
--   The orthogonal projector onto a submodule of a concrete star algebra commutes
--   with every algebra element.  The star closure supplies invariance of the
--   orthogonal complement, so this is a reducing, rather than merely invariant,
--   sector.  It is the local projector used to collapse BV03 isotypic labels by
--   correctability.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L2669-L2692
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L2669-L2692

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

theorem QEC.Bounds.BPTCommutingProjectorModel.starProjection_commute_starSubalgebraSubmodule
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B)) (W : Submodule S B) (T : S) :
    Commute (W.restrictScalars Complex).starProjection.toLinearMap
      (T : Semantics.Operator B) := by sorry
