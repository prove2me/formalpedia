-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh_tateRightIso_t__6c5694869d68
-- name    : P2M_GroundTheory_GroupCoh_tateRightIso_t__6c5694869d68
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T07:54:09.269471+00:00
-- url     : https://prove2.me/theorems/094964cd-0707-4cdb-ac63-a3e6ea2fc33b
-- title:
--   P2 M Ground Theory Group Coh tate Right Iso t  6c5694869d68: P2 M Ground Theory Group Coh tate Right Iso t  6c5694869d68
-- statement:
--   The P2 M Ground Theory Group Coh tate Right Iso t  6c5694869d68 construction uses the P2 M Ground Theory Group Coh tate Right Iso t  6c5694869d68 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupTateShift.lean#L178-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupTateShift.lean#L178-L188

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_AugmentationSES
import Definitions.Def_GroundTheory_TateCohomology_TateConnecting
import Definitions.Def_GroundTheory_TateCohomology_TateLow
import Definitions.Def_GroundTheory_TateCohomology_CupTateShift
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
variable {k G : Type u} [CommRing k] [Group G]
variable [Fintype G]
variable {E : ShortComplex (Rep.{u} k G)} (hE : E.ShortExact)
set_option backward.isDefEq.respectTransparency false

theorem P2M_GroundTheory_GroupCoh_tateRightIso_t__6c5694869d68 (B : Rep.{u} k G) (hEB : (E.map (tensorRight B)).ShortExact) (r : ℤ)
    (z : tateCohomology (E.X₃ ⊗ B) r) :
    (tateRightIso E.X₁ B (r + 1)).hom.hom ((tδ hEB r (r + 1) rfl).hom z) =
      -(tδ (shortExact_tensorRight_tensor hE B (augIdeal k G) hEB) (r + 1) (r + 1 + 1) rfl).hom
        ((tateRightIso E.X₃ B r).hom.hom z) := by sorry

alias «GroundTheory».«GroupCoh».«tateRightIso_tδ» := P2M_GroundTheory_GroupCoh_tateRightIso_t__6c5694869d68
