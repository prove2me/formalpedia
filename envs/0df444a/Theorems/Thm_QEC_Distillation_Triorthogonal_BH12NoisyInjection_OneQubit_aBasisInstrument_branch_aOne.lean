-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12NoisyInjection_OneQubit_aBasisInstrument_branch_aOne
-- name    : QEC.Distillation.Triorthogonal.BH12NoisyInjection.OneQubit.aBasisInstrument_branch_aOne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:54:53.040653+00:00
-- url     : https://prove2.me/theorems/3727dc00-97ce-42a1-b507-f7f60e713f65
-- title:
--   One Qubit: a Basis Instrument branch a One
-- statement:
--   The One Qubit construction uses the a Basis Instrument branch a One property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/NoisyInjection.lean#L418-L429
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/NoisyInjection.lean#L418-L429

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

theorem QEC.Distillation.Triorthogonal.BH12NoisyInjection.OneQubit.aBasisInstrument_branch_aOne (outcome : StabilizerOutcome) :
    aBasisInstrument.branchOperator outcome aOneDensity.toOperator =
      if outcome = .negative then aOneDensity.toOperator else 0 := by sorry
