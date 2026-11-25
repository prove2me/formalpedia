-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_measurable_tmLog
-- name    : ReciprocityTheory.MultiplicativeHeights.measurable_tmLog
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:09:26.585848+00:00
-- url     : https://prove2.me/theorems/b103a6ea-8e0a-4cac-902e-e1e692944cfa
-- title:
--   Multiplicative Heights: measurable tm Log
-- statement:
--   The Multiplicative Heights construction uses the measurable tm Log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/TorusMeanC.lean#L13-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/TorusMeanC.lean#L13-L13

import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanB
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusMeanC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Real Function
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem ReciprocityTheory.MultiplicativeHeights.measurable_tmLog (f : MvPolynomial ι ℂ) : Measurable (tmLog f) := by sorry
