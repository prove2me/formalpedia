-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_starProjection_commute_of_fullyInvariant_of_commutingStarSubalgebras
-- name    : QEC.Bounds.BPTCommutingProjectorModel.starProjection_commute_of_fullyInvariant_of_commutingStarSubalgebras
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:24:39.891228+00:00
-- url     : https://prove2.me/theorems/a7c31f9e-e384-45a5-b235-2e06054443af
-- title:
--   BPTCommuting Projector Model: star Projection commute of fully Invariant of commuting Star Subalgebras
-- statement:
--   If a second concrete star algebra commutes with the first one, the orthogonal
--   projector onto any fully invariant first-algebra submodule also commutes with
--   the second algebra.  The key point is that every second-algebra element is a
--   first-algebra module endomorphism, while star closure makes its adjoint preserve
--   the same submodule.  This is the reducing-sector form of the BV03 commutant
--   argument.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L2702-L2736
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L2702-L2736

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

theorem QEC.Bounds.BPTCommutingProjectorModel.starProjection_commute_of_fullyInvariant_of_commutingStarSubalgebras
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S R : StarSubalgebra Complex (Semantics.Operator B)) (W : Submodule S B)
    (hfullyInvariant : W.IsFullyInvariant)
    (hcommute : ∀ left : S, ∀ right : R,
      Commute (left : Semantics.Operator B) (right : Semantics.Operator B))
    (T : R) :
    Commute (W.restrictScalars Complex).starProjection.toLinearMap
      (T : Semantics.Operator B) := by sorry
