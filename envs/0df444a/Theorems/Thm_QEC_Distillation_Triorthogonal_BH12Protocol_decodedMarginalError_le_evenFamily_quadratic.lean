-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_decodedMarginalError_le_evenFamily_quadratic
-- name    : QEC.Distillation.Triorthogonal.BH12Protocol.decodedMarginalError_le_evenFamily_quadratic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:54:51.774242+00:00
-- url     : https://prove2.me/theorems/9f0e4320-6fd2-4033-bf38-b56d266a91ec
-- title:
--   BH12 Protocol: decoded Marginal Error le even Family quadratic
-- statement:
--   Every physical output's normalized error is quadratically suppressed on
--   the explicit half-error interval, with the coefficient derived from the
--   concrete BH12 enumerators.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L2580-L2601
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L2580-L2601

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

theorem QEC.Distillation.Triorthogonal.BH12Protocol.decodedMarginalError_le_evenFamily_quadratic (q : Nat)
    (p : ErrorParameter) (a : OddRow q) (hhalf : p.rate ≤ 1 / 2) :
    decodedMarginalError q p
      (rawSuccessMass_pos_of_rate_le_half q p hhalf) a ≤
      8 * ((1 + 6 * q : Nat) : ℝ) * p.rate ^ 2 := by sorry
