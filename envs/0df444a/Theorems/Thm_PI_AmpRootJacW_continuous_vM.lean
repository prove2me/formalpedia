-- Prove2me | Theorems.Thm_PI_AmpRootJacW_continuous_vM
-- name    : PI.AmpRootJacW.continuous_vM
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:19.610258+00:00
-- url     : https://prove2.me/theorems/392abb89-cba1-4a4e-b0af-b81e60fafc18
-- title:
--   Amp Root Jac W: continuous v M
-- statement:
--   The Amp Root Jac W construction uses the continuous v M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RootSubgroupJacobian/SUpPowEqZero.lean#L89-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RootSubgroupJacobian/SUpPowEqZero.lean#L89-L94

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RootSubgroupBasics_TriShear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RootSubgroupJacobian_SUpPowEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
noncomputable section
open PI PI.AmpRootJacW
variable {n : ℕ}
variable (S : Finset (Fin n × Fin n))

theorem PI.AmpRootJacW.continuous_vM : Continuous (vM S) := by sorry
