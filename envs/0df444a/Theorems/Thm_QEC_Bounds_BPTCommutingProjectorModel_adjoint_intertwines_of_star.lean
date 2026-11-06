-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_adjoint_intertwines_of_star
-- name    : QEC.Bounds.BPTCommutingProjectorModel.adjoint_intertwines_of_star
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:24:48.801739+00:00
-- url     : https://prove2.me/theorems/becd6ba8-dbb1-4c29-abbe-95cd53835357
-- title:
--   BPTCommuting Projector Model: adjoint intertwines of star
-- statement:
--   Taking adjoints preserves an intertwining equation for finite-dimensional
--   star representations.  Mathematically, applying `adjoint` to the relation for
--   `star r` reverses its two factors and involutivity returns `r`.  Its target use
--   is the polar part of the BV03 block construction: an intertwiner between two
--   sector copies has an adjoint which intertwines in the reverse direction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L2932-L2945
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L2932-L2945

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

theorem QEC.Bounds.BPTCommutingProjectorModel.adjoint_intertwines_of_star
    {R H K : Type u} [InvolutiveStar R]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteDimensional Complex H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteDimensional Complex K]
    (rhoH : R → Module.End Complex H) (rhoK : R → Module.End Complex K)
    (hH : ∀ r, LinearMap.adjoint (rhoH r) = rhoH (star r))
    (hK : ∀ r, LinearMap.adjoint (rhoK r) = rhoK (star r))
    (f : H →ₗ[Complex] K)
    (hintertwines : ∀ r, f.comp (rhoH r) = (rhoK r).comp f)
    (r : R) :
    f.adjoint.comp (rhoK r) = (rhoH r).comp f.adjoint := by sorry
