-- Prove2me | Theorems.Thm_PI_FHS_conj_wt
-- name    : PI.FHS.conj_wt
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:29:02.73796+00:00
-- url     : https://prove2.me/theorems/87532410-3852-40cc-98b4-e7aa117c56a4
-- title:
--   FHS: conj wt
-- statement:
--   The FHS construction uses the conj wt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockHarmonicSplitting/FockInnerSelfReNonneg.lean#L20-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockHarmonicSplitting/FockInnerSelfReNonneg.lean#L20-L21

import Definitions.Def_Formalism_PeriodIntegrals_JointBlockShapes_MinusPart
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockHarmonicSplitting_FockInnerSelfReNonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PI PI.FHS
variable {σ : Type*}

theorem PI.FHS.conj_wt (α : σ →₀ ℕ) : (starRingEnd ℂ) (wt α) = wt α := by sorry
