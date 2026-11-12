-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12NoisyInjection_OneQubit_aBasisDephasing_apply
-- name    : QEC.Distillation.Triorthogonal.BH12NoisyInjection.OneQubit.aBasisDephasing_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:54:21.641502+00:00
-- url     : https://prove2.me/theorems/1be9d33f-e2ce-4cb8-ac83-6e7fa9d22fb5
-- title:
--   One Qubit: a Basis Dephasing apply
-- statement:
--   Dephasing is exactly the source random-`I/A` twirl.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/NoisyInjection.lean#L477-L495
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/NoisyInjection.lean#L477-L495

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

theorem QEC.Distillation.Triorthogonal.BH12NoisyInjection.OneQubit.aBasisDephasing_apply (A : Operator QubitSpace) :
    aBasisDephasing A =
      (1 / 2 : Complex) •
        (A + aBasisObservable.comp (A.comp aBasisObservable)) := by sorry
