-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12NoisyInjection_OneQubit_sum_branchProbability
-- name    : QEC.Distillation.Triorthogonal.BH12NoisyInjection.OneQubit.sum_branchProbability
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:32:21.136143+00:00
-- url     : https://prove2.me/theorems/147fdfba-a55b-4122-83e8-11ac9386e3c3
-- title:
--   One Qubit: sum branch Probability
-- statement:
--   The One Qubit construction uses the sum branch Probability property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/NoisyInjection.lean#L529-L532
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/NoisyInjection.lean#L529-L532

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

theorem QEC.Distillation.Triorthogonal.BH12NoisyInjection.OneQubit.sum_branchProbability (p : ErrorParameter) :
    ∑ error : Fin 2, branchProbability p error = 1 := by sorry
