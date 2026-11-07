-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_exists_orthonormal_pair_fixed_of_one_lt_range_finrank
-- name    : QEC.Bounds.BPTCommutingProjectorModel.exists_orthonormal_pair_fixed_of_one_lt_range_finrank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:30:53.50532+00:00
-- url     : https://prove2.me/theorems/82255db1-5dd6-496a-821e-a61bcf0e7cca
-- title:
--   BPTCommuting Projector Model: exists orthonormal pair fixed of one lt range finrank
-- statement:
--   The BPTCommuting Projector Model construction uses the exists orthonormal pair fixed of one lt range finrank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/PartialTrace.lean#L443-L481
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/PartialTrace.lean#L443-L481

import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_Transport
import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_PartialTrace
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.exists_orthonormal_pair_fixed_of_one_lt_range_finrank
    {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    (P : Semantics.Operator H) (hP : P.IsSymmetricProjection)
    (hdim : 1 < Module.finrank Complex (LinearMap.range P)) :
    ∃ x y : H, P x = x ∧ P y = y ∧
      inner Complex x x = 1 ∧ inner Complex y y = 1 ∧
      ‖x‖ ^ 2 = 1 ∧ ‖y‖ ^ 2 = 1 ∧ inner Complex y x = 0 := by sorry
