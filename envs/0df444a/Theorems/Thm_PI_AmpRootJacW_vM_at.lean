-- Prove2me | Theorems.Thm_PI_AmpRootJacW_vM_at
-- name    : PI.AmpRootJacW.vM_at
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:06:44.702832+00:00
-- url     : https://prove2.me/theorems/899813e5-bfe5-4098-934c-c348072b055f
-- title:
--   Amp Root Jac W: v M at
-- statement:
--   The Amp Root Jac W construction uses the v M at property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RootSubgroupJacobian/SUpPowEqZero.lean#L76-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RootSubgroupJacobian/SUpPowEqZero.lean#L76-L78

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

theorem PI.AmpRootJacW.vM_at (v : S → ℂ) (q : S) : vM S v q.1.1 q.1.2 = v q := by sorry
