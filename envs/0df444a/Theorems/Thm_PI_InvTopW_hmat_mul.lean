-- Prove2me | Theorems.Thm_PI_InvTopW_hmat_mul
-- name    : PI.InvTopW.hmat_mul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:45:44.009142+00:00
-- url     : https://prove2.me/theorems/a60433ae-b712-5a86-88e4-10e1852f69cd
-- title:
--   Inv Top W: hmat mul
-- statement:
--   The Inv Top W construction uses the hmat mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantTopologyComparison/ContinuousOfHAInf.lean#L28-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantTopologyComparison/ContinuousOfHAInf.lean#L28-L28

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

theorem PI.InvTopW.hmat_mul (a b : HAd I) : hmat I (a * b) = hmat I a * hmat I b := by sorry
