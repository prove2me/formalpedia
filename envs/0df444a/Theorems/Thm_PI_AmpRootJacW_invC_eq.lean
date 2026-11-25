-- Prove2me | Theorems.Thm_PI_AmpRootJacW_invC_eq
-- name    : PI.AmpRootJacW.invC_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:23:28.324337+00:00
-- url     : https://prove2.me/theorems/4fd9691e-3a61-58c2-8398-050a8aef990f
-- title:
--   Amp Root Jac W: inv C eq
-- statement:
--   The Amp Root Jac W construction uses the inv C eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RootSubgroupJacobian/SUpPowEqZero.lean#L103-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RootSubgroupJacobian/SUpPowEqZero.lean#L103-L108

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

theorem PI.AmpRootJacW.invC_eq (hS : ∀ q ∈ S, q.1 < q.2) (v : S → ℂ) (q : S) : invC S v q = -(v q + hSh S q v) := by sorry
