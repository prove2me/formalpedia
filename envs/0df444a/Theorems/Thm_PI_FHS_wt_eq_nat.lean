-- Prove2me | Theorems.Thm_PI_FHS_wt_eq_nat
-- name    : PI.FHS.wt_eq_nat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:26.257708+00:00
-- url     : https://prove2.me/theorems/88b4e427-3a18-48bc-a458-de811e429853
-- title:
--   FHS: wt eq nat
-- statement:
--   The FHS construction uses the wt eq nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockHarmonicSplitting/FockInnerSelfReNonneg.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockHarmonicSplitting/FockInnerSelfReNonneg.lean#L13-L14

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

theorem PI.FHS.wt_eq_nat (α : σ →₀ ℕ) : wt α = ((α.prod fun _ k => k.factorial : ℕ) : ℂ) := by sorry
