-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12NoisyInjection_OneQubit_aBasisTwirl_apply
-- name    : QEC.Distillation.Triorthogonal.BH12NoisyInjection.OneQubit.aBasisTwirl_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:32:39.239188+00:00
-- url     : https://prove2.me/theorems/5c7159e8-b0fe-4222-88e9-6db6204cfb82
-- title:
--   One Qubit: a Basis Twirl apply
-- statement:
--   The One Qubit construction uses the a Basis Twirl apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/NoisyInjection.lean#L504-L508
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/NoisyInjection.lean#L504-L508

import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Definitions.Def_QEC_Coding_Stabilizer_Measurement
import Definitions.Def_QEC_Distillation_Triorthogonal_NoisyInjection
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.Triorthogonal
open QEC.Distillation.Triorthogonal.BH12NoisyInjection
open Semantics
open Coding
open Coding.PauliSymplectic
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u
open QEC.Distillation.Triorthogonal.BH12NoisyInjection.OneQubit
open Semantics.Qubit
open OneQubitMagic

theorem QEC.Distillation.Triorthogonal.BH12NoisyInjection.OneQubit.aBasisTwirl_apply (A : Operator QubitSpace) :
    aBasisTwirl A =
      (1 / 2 : Complex) •
        (A + aBasisObservable.comp (A.comp aBasisObservable)) := by sorry
