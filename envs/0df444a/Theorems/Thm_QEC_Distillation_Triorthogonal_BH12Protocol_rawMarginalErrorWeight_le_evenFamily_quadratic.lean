-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_rawMarginalErrorWeight_le_evenFamily_quadratic
-- name    : QEC.Distillation.Triorthogonal.BH12Protocol.rawMarginalErrorWeight_le_evenFamily_quadratic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:09:40.018358+00:00
-- url     : https://prove2.me/theorems/09a009c0-3d8b-419c-8cf0-db8366aedc58
-- title:
--   BH12 Protocol: raw Marginal Error Weight le even Family quadratic
-- statement:
--   The exact #754 marginal polynomial is bounded by its source-leading
--   quadratic coefficient on the explicit half-error interval.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L2453-L2545
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L2453-L2545

import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
import Definitions.Def_QEC_Distillation_Triorthogonal_NoisyInjection
import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.Triorthogonal
open QEC.Distillation.Triorthogonal.BH12Protocol
open Semantics
open Coding
open Coding.PauliSymplectic
open BH12EvenFamily
open BH12NoisyInjection
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u

theorem QEC.Distillation.Triorthogonal.BH12Protocol.rawMarginalErrorWeight_le_evenFamily_quadratic (q : Nat)
    (p : ErrorParameter) (a : OddRow q) (hhalf : p.rate ≤ 1 / 2) :
    rawMarginalErrorWeight q p a ≤
      ((1 + 6 * q : Nat) : ℝ) * p.rate ^ 2 := by sorry
