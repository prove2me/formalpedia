-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_M_image_closed_compact
-- name    : ReciprocityTheory.AnForm.M.image_closed_compact
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:54:28.07246+00:00
-- url     : https://prove2.me/theorems/621cc88f-122b-5b57-bb0b-46716a440d39
-- title:
--   M: image closed compact
-- statement:
--   The M construction uses the image closed compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/MaMeasureB.lean#L64-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/MaMeasureB.lean#L64-L69

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_MaMeasureA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_MaMeasureB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Set Filter Topology
open scoped ContDiff ENNReal NNReal
noncomputable section

theorem ReciprocityTheory.AnForm.M.image_closed_compact {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X]
    (ch : OpenPartialHomeomorph X (Fin e → ℂ)) {Z : Set X} (hZ : IsClosed Z)
    (hZs : Z ⊆ ch.source) : IsCompact (ch '' Z) ∧ ch '' Z ⊆ ch.target := by sorry
