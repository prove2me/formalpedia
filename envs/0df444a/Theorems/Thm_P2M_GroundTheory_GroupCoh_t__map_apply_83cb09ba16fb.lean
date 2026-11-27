-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh_t__map_apply_83cb09ba16fb
-- name    : P2M_GroundTheory_GroupCoh_t__map_apply_83cb09ba16fb
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:16:47.25626+00:00
-- url     : https://prove2.me/theorems/2738838d-e2b6-428b-8d13-23cf79b7dd17
-- title:
--   P2 M Ground Theory Group Coh t  map apply 83cb09ba16fb: P2 M Ground Theory Group Coh t  map apply 83cb09ba16fb
-- statement:
--   The P2 M Ground Theory Group Coh t  map apply 83cb09ba16fb construction uses the P2 M Ground Theory Group Coh t  map apply 83cb09ba16fb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupTateNatural.lean#L85-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupTateNatural.lean#L85-L89

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupTate
import Definitions.Def_GroundTheory_TateCohomology_CupTateNatural
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory MonoidalCategory groupCohomology
open GroundTheory GroundTheory.GroupCoh
universe u
variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

theorem P2M_GroundTheory_GroupCoh_t__map_apply_83cb09ba16fb {S₁ S₂ : ShortComplex (Rep.{u} k G)} (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact)
    (F : S₁ ⟶ S₂) (i : ℤ) (x : tateCohomology S₁.X₃ i) :
    (tδ h₂ i (i + 1) rfl).hom (((tateCohomologyFunctor i).map F.τ₃).hom x) =
      ((tateCohomologyFunctor (i + 1)).map F.τ₁).hom ((tδ h₁ i (i + 1) rfl).hom x) := by sorry

alias «GroundTheory».«GroupCoh».«tδ_map_apply» := P2M_GroundTheory_GroupCoh_t__map_apply_83cb09ba16fb
