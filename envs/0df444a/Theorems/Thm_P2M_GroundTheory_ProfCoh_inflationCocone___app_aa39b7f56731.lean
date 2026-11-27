-- Prove2me | Theorems.Thm_P2M_GroundTheory_ProfCoh_inflationCocone___app_aa39b7f56731
-- name    : P2M_GroundTheory_ProfCoh_inflationCocone___app_aa39b7f56731
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:54:37.260804+00:00
-- url     : https://prove2.me/theorems/92991713-0e12-4ccf-b4ef-4d17118b3eec
-- title:
--   P2 M Ground Theory Prof Coh inflation Cocone   app aa39b7f56731: P2 M Ground Theory Prof Coh inflation Cocone   app aa39b7f56731
-- statement:
--   The P2 M Ground Theory Prof Coh inflation Cocone   app aa39b7f56731 construction uses the P2 M Ground Theory Prof Coh inflation Cocone   app aa39b7f56731 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/ColimitDefs.lean#L171-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/ColimitDefs.lean#L171-L173

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains_Functoriality
import Definitions.Def_GroundTheory_ProfiniteCohomology_OpenNormal
import Definitions.Def_GroundTheory_ProfiniteCohomology_ColimitDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open CategoryTheory groupCohomology
universe u
variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G]
variable (A : Rep.{u} k G)
variable [IsTopologicalGroup G] [IsDiscreteRep A]

theorem P2M_GroundTheory_ProfCoh_inflationCocone___app_aa39b7f56731 (n : ℕ) (U : (OpenNormalSubgroup G)ᵒᵖ) :
    (inflationCocone A n).ι.app U = inflation A U.unop n := by sorry

alias «GroundTheory».«ProfCoh».«inflationCocone_ι_app» := P2M_GroundTheory_ProfCoh_inflationCocone___app_aa39b7f56731
