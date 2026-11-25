-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_IntegralRingEmbedding_val_sub_roots
-- name    : ReciprocityTheory.ChartRestriction.G.H1.IntegralRingEmbedding.val_sub_roots
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:26:01.736523+00:00
-- url     : https://prove2.me/theorems/526f7256-3874-4c66-9899-6328d1246f1a
-- title:
--   Integral Ring Embedding: val sub roots
-- statement:
--   The Integral Ring Embedding construction uses the val sub roots property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/IntegralRingEmbedding.lean#L93-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/IntegralRingEmbedding.lean#L93-L139

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

theorem ReciprocityTheory.ChartRestriction.G.H1.IntegralRingEmbedding.val_sub_roots {N : ℕ} (hN : 1 ≤ N) (hvN : v (N : F) = 0) {z z' : F} (hz : z ^ N = 1)
    (hz' : z' ^ N = 1) (hne : z ≠ z') : v (z - z') = 0 := by sorry
