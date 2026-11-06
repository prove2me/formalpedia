-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_starSubalgebra_module_isSemisimple
-- name    : QEC.Bounds.BPTCommutingProjectorModel.starSubalgebra_module_isSemisimple
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:01:19.565499+00:00
-- url     : https://prove2.me/theorems/6988f7f1-4935-4324-8e15-387f96919deb
-- title:
--   BPTCommuting Projector Model: star Subalgebra module is Semisimple
-- statement:
--   Every finite-dimensional representation of a concrete star subalgebra of
--   operators is semisimple.  The proof constructs complements as the invariant
--   orthogonal complements above.  Its target use is the isotypic decomposition
--   inside `commuting_overlap_block_factorization`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L2812-L2842
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/InteractionAlgebra.lean#L2812-L2842

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

theorem QEC.Bounds.BPTCommutingProjectorModel.starSubalgebra_module_isSemisimple
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (S : StarSubalgebra Complex (Semantics.Operator B)) :
    IsSemisimpleModule S B := by sorry
