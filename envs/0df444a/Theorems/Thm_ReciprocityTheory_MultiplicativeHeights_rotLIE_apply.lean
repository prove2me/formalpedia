-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_rotLIE_apply
-- name    : ReciprocityTheory.MultiplicativeHeights.rotLIE_apply
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:04:54.882908+00:00
-- url     : https://prove2.me/theorems/58d399d3-9b2c-5515-8d4f-fa87ebeada93
-- title:
--   Multiplicative Heights: rot LIE apply
-- statement:
--   The Multiplicative Heights construction uses the rot LIE apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SphereTorusC.lean#L73-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SphereTorusC.lean#L73-L75

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereTorusC
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
open MeasureTheory Metric
open scoped Pointwise

theorem ReciprocityTheory.MultiplicativeHeights.rotLIE_apply {n : ℕ} (u : Fin n → Circle) (x : EuclideanSpace ℂ (Fin n)) (j : Fin n) :
    (rotLIE u x).ofLp j = (u j : ℂ) * x.ofLp j := by sorry
