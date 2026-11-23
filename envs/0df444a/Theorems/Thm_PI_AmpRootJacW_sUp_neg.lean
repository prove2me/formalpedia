-- Prove2me | Theorems.Thm_PI_AmpRootJacW_sUp_neg
-- name    : PI.AmpRootJacW.sUp_neg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:39.184819+00:00
-- url     : https://prove2.me/theorems/bdde1e32-4a28-4033-9a5c-56dcc29b020e
-- title:
--   Amp Root Jac W: s Up neg
-- statement:
--   The Amp Root Jac W construction uses the s Up neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RootSubgroupJacobian/SUpPowEqZero.lean#L14-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RootSubgroupJacobian/SUpPowEqZero.lean#L14-L16

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

theorem PI.AmpRootJacW.sUp_neg {V : Matrix (Fin n) (Fin n) ℂ} (hV : SUp V) : SUp (-V) := by sorry
