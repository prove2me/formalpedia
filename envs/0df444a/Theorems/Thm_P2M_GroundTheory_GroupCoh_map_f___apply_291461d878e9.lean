-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh_map_f___apply_291461d878e9
-- name    : P2M_GroundTheory_GroupCoh_map_f___apply_291461d878e9
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:52:22.654784+00:00
-- url     : https://prove2.me/theorems/253ad0ab-fa05-5367-999a-1b873c8d6d74
-- title:
--   P2 M Ground Theory Group Coh map f   apply 291461d878e9: P2 M Ground Theory Group Coh map f   apply 291461d878e9
-- statement:
--   The P2 M Ground Theory Group Coh map f   apply 291461d878e9 construction uses the P2 M Ground Theory Group Coh map f   apply 291461d878e9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/SplittingCohTrivial.lean#L32-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/SplittingCohTrivial.lean#L32-L35

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

theorem P2M_GroundTheory_GroupCoh_map_f___apply_291461d878e9 (i j : ℕ) (hij : i + 1 = j) (z : groupCohomology X.X₃ i) :
    map (MonoidHom.id H) X.f j (δ hX i j hij z) = 0 := by sorry

alias «GroundTheory».«GroupCoh».«map_f_δ_apply» := P2M_GroundTheory_GroupCoh_map_f___apply_291461d878e9
