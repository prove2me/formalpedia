-- Prove2me | Theorems.Thm_PI_FHS_wt_add_single
-- name    : PI.FHS.wt_add_single
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:32:04.273259+00:00
-- url     : https://prove2.me/theorems/d6837426-9bd4-556e-8a6b-dd09f00aded6
-- title:
--   FHS: wt add single
-- statement:
--   The FHS construction uses the wt add single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockHarmonicSplitting/FockInnerSelfReNonneg.lean#L162-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockHarmonicSplitting/FockInnerSelfReNonneg.lean#L162-L183

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

theorem PI.FHS.wt_add_single [Fintype σ] [DecidableEq σ] (β : σ →₀ ℕ) (l : σ) :
    wt (β + Finsupp.single l 1) = ((β l + 1 : ℕ) : ℂ) * wt β := by sorry
