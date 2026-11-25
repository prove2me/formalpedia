-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh_coe_mapCocycles__conj_514c62901d51
-- name    : P2M_GroundTheory_GroupCoh_coe_mapCocycles__conj_514c62901d51
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:08:07.770884+00:00
-- url     : https://prove2.me/theorems/c6050149-5b89-5e85-a24a-91ec0349ac28
-- title:
--   P2 M Ground Theory Group Coh coe map Cocycles  conj 514c62901d51: P2 M Ground Theory Group Coh coe map Cocycles  conj 514c62901d51
-- statement:
--   The P2 M Ground Theory Group Coh coe map Cocycles  conj 514c62901d51 construction uses the P2 M Ground Theory Group Coh coe map Cocycles  conj 514c62901d51 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/ConjAction.lean#L59-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/ConjAction.lean#L59-L60

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_ConjAction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.GroupCoh
open CategoryTheory groupCohomology Rep
universe u
variable {k G : Type u} [CommRing k] [Group G] (A : Rep k G) (S : Subgroup G) [S.Normal]

theorem P2M_GroundTheory_GroupCoh_coe_mapCocycles__conj_514c62901d51 (g : G) (f : cocycles₁ (res S.subtype A)) (s : S) :
    mapCocycles₁ (conjHom S g) (conjMor A S g) f s = A.ρ g (f (conjHom S g s)) := by sorry

alias «GroundTheory».«GroupCoh».«coe_mapCocycles₁_conj» := P2M_GroundTheory_GroupCoh_coe_mapCocycles__conj_514c62901d51
