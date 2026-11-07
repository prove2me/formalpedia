-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LiftedProductActionBridge_retained_checks_orthogonal_of_auxiliary_disjoint
-- name    : QEC.Coding.QuantumTanner.LiftedProductActionBridge.retained_checks_orthogonal_of_auxiliary_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:11:00.512095+00:00
-- url     : https://prove2.me/theorems/9148afbb-3c40-450c-9b14-77fbd397a151
-- title:
--   Lifted Product Action Bridge: retained checks orthogonal of auxiliary disjoint
-- statement:
--   Puncturing retains orthogonality exactly when the deleted supports contribute zero.
--   This lemma alone is not a claim about arbitrary CSS puncturing; the selected
--   families must establish its pointwise hypothesis from local dual checks.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductActionBridge.lean#L247-L271
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductActionBridge.lean#L247-L271

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
import Definitions.Def_QEC_Coding_QuantumTanner_LiftedProductRestriction
import Definitions.Def_QEC_Coding_QuantumTanner_LiftedProductActionBridge
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LiftedProductActionBridge
open QEC.Coding.LiftedProduct
open QEC.Coding.QuantumTanner.LiftedProductRestriction
noncomputable section
variable {G A B C D : Type*} [Group G] [Fintype G] [DecidableEq G]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]
variable {C' D' : Type*} [Fintype C'] [Fintype D']

theorem QEC.Coding.QuantumTanner.LiftedProductActionBridge.retained_checks_orthogonal_of_auxiliary_disjoint
    (hA : Matrix C A (ZMod 2)) (hB : Matrix D B (ZMod 2)) (a : A → G) (b : B → G)
    (U : C2Index B (Bool × C) G → ZMod 2)
    (V : C0Index (Bool × D) A G → ZMod 2)
    (hAux : ∀ d c g, zWord hA hB a b U (auxiliaryCoordinate c d g) = 0 ∨
      xWord hA hB a b V (auxiliaryCoordinate c d g) = 0) :
    (∑ j : B, ∑ i : A, ∑ g : G,
      zWord hA hB a b U (retainedCoordinate i j g) *
        xWord hA hB a b V (retainedCoordinate i j g)) = 0 := by sorry
