-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_syndromeOutcome_eq_rejected_iff
-- name    : QEC.Distillation.Triorthogonal.BH12Protocol.syndromeOutcome_eq_rejected_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:59:09.825008+00:00
-- url     : https://prove2.me/theorems/4c2e94c3-f6ca-4877-ae26-4df320591e7c
-- title:
--   BH12 Protocol: syndrome Outcome eq rejected iff
-- statement:
--   The BH12 Protocol construction uses the syndrome Outcome eq rejected iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L114-L116
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L114-L116

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

theorem QEC.Distillation.Triorthogonal.BH12Protocol.syndromeOutcome_eq_rejected_iff (syndrome : Syndrome) :
    syndromeOutcome syndrome = .rejected ↔ syndrome ≠ trivialSyndrome := by sorry
