-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12NoisyInjection_OneQubit_aOneDensity_rankOne
-- name    : QEC.Distillation.Triorthogonal.BH12NoisyInjection.OneQubit.aOneDensity_rankOne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:28:56.010198+00:00
-- url     : https://prove2.me/theorems/4078c575-56af-4379-b762-7799a4a884a2
-- title:
--   One Qubit: a One Density rank One
-- statement:
--   The One Qubit construction uses the a One Density rank One property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/NoisyInjection.lean#L348-L360
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/NoisyInjection.lean#L348-L360

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

theorem QEC.Distillation.Triorthogonal.BH12NoisyInjection.OneQubit.aOneDensity_rankOne :
    aOneDensity.toOperator =
      (InnerProductSpace.rankOne Complex aOneState aOneState).toLinearMap := by sorry
