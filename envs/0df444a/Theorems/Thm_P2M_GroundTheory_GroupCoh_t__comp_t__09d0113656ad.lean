-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh_t__comp_t__09d0113656ad
-- name    : P2M_GroundTheory_GroupCoh_t__comp_t__09d0113656ad
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:55:05.307605+00:00
-- url     : https://prove2.me/theorems/ae97c81f-c61d-4ad2-aa53-cd9f97dabe67
-- title:
--   P2 M Ground Theory Group Coh t  comp t  09d0113656ad: P2 M Ground Theory Group Coh t  comp t  09d0113656ad
-- statement:
--   The P2 M Ground Theory Group Coh t  comp t  09d0113656ad construction uses the P2 M Ground Theory Group Coh t  comp t  09d0113656ad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateConnecting.lean#L204-L283
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateConnecting.lean#L204-L283

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupConnecting
import Definitions.Def_GroundTheory_TateCohomology_TateConnecting
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory groupCohomology
open GroundTheory GroundTheory.GroupCoh
universe u
variable {k G : Type u} [CommRing k] [Group G] [Fintype G]
variable (Q : ShortComplex (ShortComplex (Rep k G)))
  (hR₁ : Q.X₁.ShortExact) (hR₂ : Q.X₂.ShortExact) (hR₃ : Q.X₃.ShortExact)
  (hC₁ : (Q.map ShortComplex.π₁).ShortExact) (hC₂ : (Q.map ShortComplex.π₂).ShortExact)
  (hC₃ : (Q.map ShortComplex.π₃).ShortExact)
include hR₂ hC₂
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

theorem P2M_GroundTheory_GroupCoh_t__comp_t__09d0113656ad (p : ℤ) :
    tδ hC₃ p (p + 1) rfl ≫ tδ hR₁ (p + 1) (p + 1 + 1) rfl =
      -(tδ hR₃ p (p + 1) rfl ≫ tδ hC₁ (p + 1) (p + 1 + 1) rfl) := by sorry

alias «GroundTheory».«GroupCoh».«tδ_comp_tδ» := P2M_GroundTheory_GroupCoh_t__comp_t__09d0113656ad
