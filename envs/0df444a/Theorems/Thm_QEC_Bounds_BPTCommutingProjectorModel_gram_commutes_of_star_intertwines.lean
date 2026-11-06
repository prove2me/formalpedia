-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_gram_commutes_of_star_intertwines
-- name    : QEC.Bounds.BPTCommutingProjectorModel.gram_commutes_of_star_intertwines
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:08:55.6002+00:00
-- url     : https://prove2.me/theorems/c74ebe18-794e-43fc-ae23-ed53601628ff
-- title:
--   BPTCommuting Projector Model: gram commutes of star intertwines
-- statement:
--   The positive Gram operator of a star-intertwiner lies in the commutant of the
--   source action.  Consequently its finite-dimensional polar support and the
--   resulting partial isometry remain inside a single interaction-algebra sector.
--   This supplies the unitary-intertwiner step needed to turn the isotypic matrix
--   description into the actual BV03 tensor-block decomposition.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L2954-L2974
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L2954-L2974

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

theorem QEC.Bounds.BPTCommutingProjectorModel.gram_commutes_of_star_intertwines
    {R H K : Type u} [InvolutiveStar R]
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteDimensional Complex H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteDimensional Complex K]
    (rhoH : R → Module.End Complex H) (rhoK : R → Module.End Complex K)
    (hH : ∀ r, LinearMap.adjoint (rhoH r) = rhoH (star r))
    (hK : ∀ r, LinearMap.adjoint (rhoK r) = rhoK (star r))
    (f : H →ₗ[Complex] K)
    (hintertwines : ∀ r, f.comp (rhoH r) = (rhoK r).comp f)
    (r : R) :
    Commute (f.adjoint.comp f) (rhoH r) := by sorry
