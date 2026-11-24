-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_exists_rightInverse_weierstrassExp
-- name    : ReciprocityTheory.ChartRestriction.L1.exists_rightInverse_weierstrassExp
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:44:45.553025+00:00
-- url     : https://prove2.me/theorems/29fad296-2228-4d46-b39f-3ecaa5817d54
-- title:
--   L1: exists right Inverse weierstrass Exp
-- statement:
--   The L1 construction uses the exists right Inverse weierstrass Exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/CoeffOneSubstOfConstantCoeffEqZero.lean#L42-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/CoeffOneSubstOfConstantCoeffEqZero.lean#L42-L43

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

theorem ReciprocityTheory.ChartRestriction.L1.exists_rightInverse_weierstrassExp : ∃ t : PowerSeries K, constantCoeff t = 0 ∧ (uSer g2 g3).subst t = X := by sorry
