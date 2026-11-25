-- Prove2me | Theorems.Thm_PI_AmpRootJacW_continuous_hSh
-- name    : PI.AmpRootJacW.continuous_hSh
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:23:26.060202+00:00
-- url     : https://prove2.me/theorems/61e2bb73-23ec-44c8-95a2-a3606023c22d
-- title:
--   Amp Root Jac W: continuous h Sh
-- statement:
--   The Amp Root Jac W construction uses the continuous h Sh property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RootSubgroupJacobian/SUpPowEqZero.lean#L130-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RootSubgroupJacobian/SUpPowEqZero.lean#L130-L134

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

theorem PI.AmpRootJacW.continuous_hSh (q : S) : Continuous (hSh S q) := by sorry
