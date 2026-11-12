-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Protocol_finite_one_sub_sum_le_product
-- name    : QEC.Distillation.HH18Protocol.finite_one_sub_sum_le_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:32:32.443204+00:00
-- url     : https://prove2.me/theorems/e275113f-2fdc-43da-b773-d3f3621b0c33
-- title:
--   HH18 Protocol: finite one sub sum le product
-- statement:
--   Abstract finite product-versus-loss-sum accounting.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L596-L618
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/Protocol.lean#L596-L618

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_OutputHandoff
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_Protocol
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Protocol
open Coding Semantics
open Coding.PauliSymplectic
open Semantics.Qubit
open scoped BigOperators
universe u
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Protocol.instProtocolClassicalDecidable
attribute [local instance] QEC.Distillation.HH18Protocol.instProtocolClassicalDecidable
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit
open OneQubitMagic

theorem QEC.Distillation.HH18Protocol.finite_one_sub_sum_le_product {ι : Type*} (s : Finset ι)
    (loss : ι → ℝ) (hlossNonneg : ∀ i ∈ s, 0 ≤ loss i)
    (hlossLeOne : ∀ i ∈ s, loss i ≤ 1) :
    1 - ∑ i ∈ s, loss i ≤ ∏ i ∈ s, (1 - loss i) := by sorry
