-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_syndromeOutcome_eq_accepted_iff
-- name    : QEC.Distillation.Triorthogonal.BH12Protocol.syndromeOutcome_eq_accepted_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:59:04.787485+00:00
-- url     : https://prove2.me/theorems/e3a78a6a-187c-4d01-badb-61300ca5ee67
-- title:
--   BH12 Protocol: syndrome Outcome eq accepted iff
-- statement:
--   The BH12 Protocol construction uses the syndrome Outcome eq accepted iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L110-L112
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L110-L112

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

theorem QEC.Distillation.Triorthogonal.BH12Protocol.syndromeOutcome_eq_accepted_iff (syndrome : Syndrome) :
    syndromeOutcome syndrome = .accepted ↔ syndrome = trivialSyndrome := by sorry
