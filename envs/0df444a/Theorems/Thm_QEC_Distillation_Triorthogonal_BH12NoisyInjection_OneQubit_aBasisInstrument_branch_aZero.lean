-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12NoisyInjection_OneQubit_aBasisInstrument_branch_aZero
-- name    : QEC.Distillation.Triorthogonal.BH12NoisyInjection.OneQubit.aBasisInstrument_branch_aZero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:31:06.08587+00:00
-- url     : https://prove2.me/theorems/f1cd3f13-264d-4826-a085-128ce5b2cdd2
-- title:
--   One Qubit: a Basis Instrument branch a Zero
-- statement:
--   The One Qubit construction uses the a Basis Instrument branch a Zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/NoisyInjection.lean#L374-L385
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/NoisyInjection.lean#L374-L385

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

theorem QEC.Distillation.Triorthogonal.BH12NoisyInjection.OneQubit.aBasisInstrument_branch_aZero (outcome : StabilizerOutcome) :
    aBasisInstrument.branchOperator outcome aZeroDensity.toOperator =
      if outcome = .positive then aZeroDensity.toOperator else 0 := by sorry
