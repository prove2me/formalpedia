-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh___map_g_apply_e86f9a071593
-- name    : P2M_GroundTheory_GroupCoh___map_g_apply_e86f9a071593
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T07:53:43.10783+00:00
-- url     : https://prove2.me/theorems/5c23f5fe-dfe9-4427-a076-2a13c31bf873
-- title:
--   P2 M Ground Theory Group Coh   map g apply e86f9a071593: P2 M Ground Theory Group Coh   map g apply e86f9a071593
-- statement:
--   The P2 M Ground Theory Group Coh   map g apply e86f9a071593 construction uses the P2 M Ground Theory Group Coh   map g apply e86f9a071593 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/SplittingCohTrivial.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/SplittingCohTrivial.lean#L25-L28

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_SplittingModule
import Definitions.Def_GroundTheory_TateCohomology_CohTrivial
import Definitions.Def_GroundTheory_TateCohomology_ResCores
import Definitions.Def_GroundTheory_TateCohomology_SplittingCohTrivial
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
variable {k H : Type u} [CommRing k] [Group H] {X : ShortComplex (Rep.{u} k H)} (hX : X.ShortExact)
include hX

theorem P2M_GroundTheory_GroupCoh___map_g_apply_e86f9a071593 (i j : ℕ) (hij : i + 1 = j) (x : groupCohomology X.X₂ i) :
    δ hX i j hij (map (MonoidHom.id H) X.g i x) = 0 := by sorry

alias «GroundTheory».«GroupCoh».«δ_map_g_apply» := P2M_GroundTheory_GroupCoh___map_g_apply_e86f9a071593
