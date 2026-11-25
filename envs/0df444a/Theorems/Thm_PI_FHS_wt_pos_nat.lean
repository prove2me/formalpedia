-- Prove2me | Theorems.Thm_PI_FHS_wt_pos_nat
-- name    : PI.FHS.wt_pos_nat
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:29:46.222108+00:00
-- url     : https://prove2.me/theorems/65bbdace-652f-48a7-a7b9-5519225ef688
-- title:
--   FHS: wt pos nat
-- statement:
--   The FHS construction uses the wt pos nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockHarmonicSplitting/FockInnerSelfReNonneg.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockHarmonicSplitting/FockInnerSelfReNonneg.lean#L16-L18

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

theorem PI.FHS.wt_pos_nat (α : σ →₀ ℕ) : 0 < (α.prod fun _ k => k.factorial : ℕ) := by sorry
