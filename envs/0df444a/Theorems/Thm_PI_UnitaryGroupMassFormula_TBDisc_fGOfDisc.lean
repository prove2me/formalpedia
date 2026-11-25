-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_TBDisc_fGOfDisc
-- name    : PI.UnitaryGroupMassFormula.TBDisc.fGOfDisc
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:40:12.608799+00:00
-- url     : https://prove2.me/theorems/0a1d5a2a-e764-4a1e-aaf5-b54fecb426ef
-- title:
--   TBDisc: f GOf Disc
-- statement:
--   The TBDisc construction uses the f GOf Disc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/UniformDiscreteness/FgOfUnifDiscrete.lean#L120-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantLemmas/UniformDiscreteness/FgOfUnifDiscrete.lean#L120-L120

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_RatIntUnifDiscrete
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_UniformDiscreteness_FgOfUnifDiscrete
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.TBDisc
open NumberField ReciprocityTheory.ChartRestriction.G.TB

theorem PI.UnitaryGroupMassFormula.TBDisc.fGOfDisc : FGOfDiscSt := by sorry
