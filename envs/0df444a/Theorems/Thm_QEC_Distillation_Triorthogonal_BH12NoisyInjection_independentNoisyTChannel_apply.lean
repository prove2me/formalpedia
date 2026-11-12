-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12NoisyInjection_independentNoisyTChannel_apply
-- name    : QEC.Distillation.Triorthogonal.BH12NoisyInjection.independentNoisyTChannel_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:55:05.014207+00:00
-- url     : https://prove2.me/theorems/840b2b27-4583-4419-8242-9bed6d2dc64d
-- title:
--   BH12 Noisy Injection: independent Noisy TChannel apply
-- statement:
--   The independent channel has one literal Kraus branch per physical error word.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/NoisyInjection.lean#L819-L851
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/NoisyInjection.lean#L819-L851

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
variable {Index : Type u} [Fintype Index] [DecidableEq Index]

theorem QEC.Distillation.Triorthogonal.BH12NoisyInjection.independentNoisyTChannel_apply (p : ErrorParameter)
    (A : Operator (Qubit.QubitRegister Index)) :
    independentNoisyTChannel (Index := Index) p A =
      ∑ error : Word (ZMod 2) Index,
        (errorWordProbability p error : Complex) •
          (toQubitOperator (cssZCheck error)).comp
            ((allSiteT (Index := Index)).conjOperator A |>.comp
              (toQubitOperator (cssZCheck error))) := by sorry
