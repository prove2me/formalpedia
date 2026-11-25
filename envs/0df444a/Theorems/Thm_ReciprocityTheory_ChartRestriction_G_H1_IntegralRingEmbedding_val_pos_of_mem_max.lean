-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_IntegralRingEmbedding_val_pos_of_mem_max
-- name    : ReciprocityTheory.ChartRestriction.G.H1.IntegralRingEmbedding.val_pos_of_mem_max
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:25:25.775331+00:00
-- url     : https://prove2.me/theorems/0401d6fe-8307-5b39-86e7-dc978e8fd9d3
-- title:
--   Integral Ring Embedding: val pos of mem max
-- statement:
--   The Integral Ring Embedding construction uses the val pos of mem max property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/IntegralRingEmbedding.lean#L66-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/IntegralRingEmbedding.lean#L66-L70

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_NakayamaChar
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_IntegralRingEmbedding
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1 ReciprocityTheory.ChartRestriction.G.H1.IntegralRingEmbedding
open Module
variable {F : Type} [Field F] (v : AddValuation F (WithTop ℚ))

theorem ReciprocityTheory.ChartRestriction.G.H1.IntegralRingEmbedding.val_pos_of_mem_max (x : intRing v) (hx : x ∈ IsLocalRing.maximalIdeal (intRing v)) :
    0 < v (x : F) := by sorry
