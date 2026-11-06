-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_starProjection_commute_of_invariant_of_orthogonalInvariant
-- name    : QEC.Bounds.BPTCommutingProjectorModel.starProjection_commute_of_invariant_of_orthogonalInvariant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:07:05.402746+00:00
-- url     : https://prove2.me/theorems/53225b0d-9449-4790-9349-da28649e9224
-- title:
--   BPTCommuting Projector Model: star Projection commute of invariant of orthogonal Invariant
-- statement:
--   If an operator reduces a finite-dimensional Hilbert subspace, then it commutes
--   with that subspace's orthogonal projector.  This turns the representation-
--   theoretic isotypic summands below into honest local sector projectors, which is
--   the form needed by the correctability/no-information argument.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L2620-L2633
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L2620-L2633

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

theorem QEC.Bounds.BPTCommutingProjectorModel.starProjection_commute_of_invariant_of_orthogonalInvariant
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (W : Submodule Complex B) (T : Semantics.Operator B)
    (hW : ∀ ⦃vector : B⦄, vector ∈ W → T vector ∈ W)
    (hWperp : ∀ ⦃vector : B⦄, vector ∈ Wᗮ → T vector ∈ Wᗮ) :
    Commute W.starProjection.toLinearMap T := by sorry
