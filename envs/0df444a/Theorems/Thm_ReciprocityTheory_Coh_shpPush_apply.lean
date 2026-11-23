-- Prove2me | Theorems.Thm_ReciprocityTheory_Coh_shpPush_apply
-- name    : ReciprocityTheory.Coh.shpPush_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:33:22.041019+00:00
-- url     : https://prove2.me/theorems/74858252-a4fc-47a9-8a59-712c81bc7b77
-- title:
--   Coh: shp Push apply
-- statement:
--   The Coh construction uses the shp Push apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/Shapiro.lean#L89-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GroupCohomology/Shapiro.lean#L89-L89

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogExistsStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_DEqZeroOfMemB
import Definitions.Def_ReciprocityTheory_GroupCohomology_HomogIso
import Definitions.Def_ReciprocityTheory_GroupCohomology_PrismOpZeroEval
import Definitions.Def_ReciprocityTheory_GroupCohomology_Shapiro
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open ReciprocityTheory.Gal Cx Function
noncomputable section
universe u
variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {U : Subgroup G} {M : TRep R U} {C : TRep R G} (ev : Pair C M) (hφ : ev.φ = U.subtype)

theorem ReciprocityTheory.Coh.shpPush_apply (n : ℕ) (F : hcoch C G n) (x) : (shpPush ev hφ n F).1 x = ev.u (F.1 x) := by sorry
