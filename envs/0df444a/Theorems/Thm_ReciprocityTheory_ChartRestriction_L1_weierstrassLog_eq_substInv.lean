-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_weierstrassLog_eq_substInv
-- name    : ReciprocityTheory.ChartRestriction.L1.weierstrassLog_eq_substInv
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T21:45:01.065981+00:00
-- url     : https://prove2.me/theorems/a8393ef9-83fb-4901-a968-0a541874ca40
-- title:
--   L1: weierstrass Log eq subst Inv
-- statement:
--   The L1 construction uses the weierstrass Log eq subst Inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/CoeffOneSubstOfConstantCoeffEqZero.lean#L67-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/CoeffOneSubstOfConstantCoeffEqZero.lean#L67-L67

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_FgDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_CoeffOneSubstOfConstantCoeffEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
variable {K : Type} [Field K] (g2 g3 : K)

theorem ReciprocityTheory.ChartRestriction.L1.weierstrassLog_eq_substInv : lgS g2 g3 = (uSer g2 g3).substInvOfIsUnit (isUnit_coeff_one_weierstrassExp g2 g3) := by sorry
