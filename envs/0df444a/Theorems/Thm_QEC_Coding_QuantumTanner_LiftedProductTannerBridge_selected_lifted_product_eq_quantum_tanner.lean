-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LiftedProductTannerBridge_selected_lifted_product_eq_quantum_tanner
-- name    : QEC.Coding.QuantumTanner.LiftedProductTannerBridge.selected_lifted_product_eq_quantum_tanner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:10:32.798125+00:00
-- url     : https://prove2.me/theorems/135bc1de-2cd4-4242-b01c-79b74245394e
-- title:
--   Lifted Product Tanner Bridge: selected lifted product eq quantum tanner
-- statement:
--   Deterministic bridge for the selected canonical lifted-product construction.
--   Both check-space equalities are proved against the span of actual local
--   extensions on labelled squares. The only code premises specify local dual
--   parity checks; they are not a global construction-equivalence certificate.
--   No spectral bound, expansion, no-conjugacy, or goodness claim is made.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductTannerBridge.lean#L352-L379
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductTannerBridge.lean#L352-L379

import Definitions.Def_QEC_Coding_QuantumTanner_LiftedProductTensorBridge
import Definitions.Def_QEC_Coding_QuantumTanner_LiftedProductTannerBridge
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LiftedProductTannerBridge
open Classical
open LiftedProductRestriction LiftedProductActionBridge LiftedProductTensorBridge
universe v
variable {G A B C D C' D' : Type v} [Group G] [Fintype G] [DecidableEq G]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]
  [Fintype C'] [DecidableEq C'] [Fintype D'] [DecidableEq D']

theorem QEC.Coding.QuantumTanner.LiftedProductTannerBridge.selected_lifted_product_eq_quantum_tanner
    (hA : Matrix C A (ZMod 2)) (hB : Matrix D B (ZMod 2))
    (gA : Matrix C' A (ZMod 2)) (gB : Matrix D' B (ZMod 2))
    (a : A → G) (b : B → G)
    (hDualA : parityCheckKernelCode (Matrix.toLin' gA) =
      (parityCheckKernelCode (Matrix.toLin' hA)).dual)
    (hDualB : parityCheckKernelCode (Matrix.toLin' gB) =
      (parityCheckKernelCode (Matrix.toLin' hB)).dual) :
    let CA := parityCheckKernelCode (Matrix.toLin' gA)
    let CB := parityCheckKernelCode (Matrix.toLin' hB)
    Set.range (selectedZWord hA hB gB a b) =
      (tannerZChecks a b (tensorCode CA CB)).carrier ∧
    Set.range (selectedXWord hA hB gA a b) =
      (tannerXChecks a b (tensorCode CA.dual CB.dual)).carrier ∧
    ∀ U V, (∑ j : B, ∑ i : A, ∑ g : G,
      selectedZWord hA hB gB a b U (i, j, g) *
        selectedXWord hA hB gA a b V (i, j, g)) = 0 := by sorry
