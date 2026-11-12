-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_bh12MagicStateDistillationProtocol_quadratic
-- name    : QEC.Distillation.Triorthogonal.BH12Protocol.bh12MagicStateDistillationProtocol_quadratic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:54:37.518418+00:00
-- url     : https://prove2.me/theorems/2443b04b-158c-4376-8a1d-ad152cf047a2
-- title:
--   BH12 Protocol: bh12 Magic State Distillation Protocol quadratic
-- statement:
--   The #457 wrapper inherits the physical BH12 quadratic marginal theorem;
--   the coefficient is proved from the actual #754 enumerators above.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L3274-L3280
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L3274-L3280

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

theorem QEC.Distillation.Triorthogonal.BH12Protocol.bh12MagicStateDistillationProtocol_quadratic (q : Nat)
    (p : ErrorParameter) (a : OddRow q) (hhalf : p.rate ≤ 1 / 2) :
    (bh12MagicStateDistillationProtocol q p a
      (rawSuccessMass_pos_of_rate_le_half q p hhalf)).successfulOutputError ≤
      8 * ((1 + 6 * q : Nat) : ℝ) * p.rate ^ 2 := by sorry
