-- Prove2me | Theorems.Thm_PI_InvTopW_continuous_hmat
-- name    : PI.InvTopW.continuous_hmat
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:46:53.003504+00:00
-- url     : https://prove2.me/theorems/7934afcc-7880-4aa6-aad9-f5525124359a
-- title:
--   Inv Top W: continuous hmat
-- statement:
--   The Inv Top W construction uses the continuous hmat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantTopologyComparison/ContinuousOfHAInf.lean#L22-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantTopologyComparison/ContinuousOfHAInf.lean#L22-L26

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_EntriesLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantTopologyComparison_ContinuousOfHAInf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.InvTopW
open NumberField IsDedekindDomain Matrix Topology Filter
open scoped TensorProduct Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.MainNotions.S (AutInst uMat)
open Formalism.L2.SG.AdBridge PI.AdBridgeSteps
variable (I : AutInst)

theorem PI.InvTopW.continuous_hmat : Continuous (fun h : HAd I => hmat I h) := by sorry
