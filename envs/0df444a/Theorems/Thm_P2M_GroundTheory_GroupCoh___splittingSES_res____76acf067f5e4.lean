-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh___splittingSES_res____76acf067f5e4
-- name    : P2M_GroundTheory_GroupCoh___splittingSES_res____76acf067f5e4
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:19:44.805733+00:00
-- url     : https://prove2.me/theorems/c4dfdbfd-006d-430b-ab94-d6c2fe2941c0
-- title:
--   P2 M Ground Theory Group Coh   splitting SES res    76acf067f5e4: P2 M Ground Theory Group Coh   splitting SES res    76acf067f5e4
-- statement:
--   The P2 M Ground Theory Group Coh   splitting SES res    76acf067f5e4 construction uses the P2 M Ground Theory Group Coh   splitting SES res    76acf067f5e4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/SplittingModule.lean#L71-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/SplittingModule.lean#L71-L100

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_PullbackExtension
import Definitions.Def_GroundTheory_TateCohomology_AugTrivial
import Definitions.Def_GroundTheory_TateCohomology_DeltaMap
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Definitions.Def_GroundTheory_TateCohomology_TateConnecting
import Definitions.Def_GroundTheory_TateCohomology_SplittingModule
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory Limits groupCohomology Rep
open GroundTheory GroundTheory.GroupCoh
universe u
variable {k G : Type u} [CommRing k] [Group G] [Fintype G] (M : Rep.{u} k G)
  (u : groupCohomology M 2)

theorem P2M_GroundTheory_GroupCoh___splittingSES_res____76acf067f5e4 {H : Type u} [Group H] (φ : H →* G) :
    δ ((shortExact_res φ).2 (splittingSES_shortExact M u)) 1 2 rfl
      (δ (augTrivSES_res_shortExact k φ) 0 1 rfl ((H0Iso _).inv (oneInvariant k φ))) =
    map φ (𝟙 (res φ M)) 2 u := by sorry

alias «GroundTheory».«GroupCoh».«δ_splittingSES_res_δ₀» := P2M_GroundTheory_GroupCoh___splittingSES_res____76acf067f5e4
