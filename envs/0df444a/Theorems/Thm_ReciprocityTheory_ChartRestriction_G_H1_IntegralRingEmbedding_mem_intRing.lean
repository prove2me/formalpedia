-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_IntegralRingEmbedding_mem_intRing
-- name    : ReciprocityTheory.ChartRestriction.G.H1.IntegralRingEmbedding.mem_intRing
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:50:17.13281+00:00
-- url     : https://prove2.me/theorems/8d27778e-b9fb-4b1f-8b87-398f75d03dc0
-- title:
--   Integral Ring Embedding: mem int Ring
-- statement:
--   The Integral Ring Embedding construction uses the mem int Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/IntegralRingEmbedding.lean#L50-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/IntegralRingEmbedding.lean#L50-L50

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

theorem ReciprocityTheory.ChartRestriction.G.H1.IntegralRingEmbedding.mem_intRing {a : F} : a ∈ intRing v ↔ 0 ≤ v a := by sorry
