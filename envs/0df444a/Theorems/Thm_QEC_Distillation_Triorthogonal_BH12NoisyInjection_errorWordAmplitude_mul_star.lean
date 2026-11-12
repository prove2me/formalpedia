-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12NoisyInjection_errorWordAmplitude_mul_star
-- name    : QEC.Distillation.Triorthogonal.BH12NoisyInjection.errorWordAmplitude_mul_star
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:34:04.133479+00:00
-- url     : https://prove2.me/theorems/f382795c-f839-4746-ab54-30069ba73ed1
-- title:
--   BH12 Noisy Injection: error Word Amplitude mul star
-- statement:
--   The BH12 Noisy Injection construction uses the error Word Amplitude mul star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/NoisyInjection.lean#L781-L785
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/NoisyInjection.lean#L781-L785

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
omit [DecidableEq Index]

theorem QEC.Distillation.Triorthogonal.BH12NoisyInjection.errorWordAmplitude_mul_star (p : ErrorParameter)
    (error : Word (ZMod 2) Index) :
    errorWordAmplitude p error * star (errorWordAmplitude p error) =
      (errorWordProbability p error : Complex) := by sorry
