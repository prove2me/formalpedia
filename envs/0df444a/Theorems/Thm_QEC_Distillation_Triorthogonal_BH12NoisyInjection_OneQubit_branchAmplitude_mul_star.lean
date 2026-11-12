-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12NoisyInjection_OneQubit_branchAmplitude_mul_star
-- name    : QEC.Distillation.Triorthogonal.BH12NoisyInjection.OneQubit.branchAmplitude_mul_star
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:32:51.024929+00:00
-- url     : https://prove2.me/theorems/3e7bf4aa-e441-4e0a-a3e4-c0df99bb0d79
-- title:
--   One Qubit: branch Amplitude mul star
-- statement:
--   The One Qubit construction uses the branch Amplitude mul star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/NoisyInjection.lean#L550-L553
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/NoisyInjection.lean#L550-L553

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

theorem QEC.Distillation.Triorthogonal.BH12NoisyInjection.OneQubit.branchAmplitude_mul_star (p : ErrorParameter) (error : Fin 2) :
    branchAmplitude p error * star (branchAmplitude p error) =
      (branchProbability p error : Complex) := by sorry
