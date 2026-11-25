-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh_tateLeftIso_t___8e34a8e92af3
-- name    : P2M_GroundTheory_GroupCoh_tateLeftIso_t___8e34a8e92af3
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T07:55:12.024686+00:00
-- url     : https://prove2.me/theorems/6c9eb84a-0aef-4bcb-9240-8aa2e572a945
-- title:
--   P2 M Ground Theory Group Coh tate Left Iso t   8e34a8e92af3: P2 M Ground Theory Group Coh tate Left Iso t   8e34a8e92af3
-- statement:
--   The P2 M Ground Theory Group Coh tate Left Iso t   8e34a8e92af3 construction uses the P2 M Ground Theory Group Coh tate Left Iso t   8e34a8e92af3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupTateShift.lean#L220-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupTateShift.lean#L220-L231

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

theorem P2M_GroundTheory_GroupCoh_tateLeftIso_t___8e34a8e92af3 (A : Rep.{u} k G) (hAE : (E.map (tensorLeft A)).ShortExact) (r : ℤ)
    (z : tateCohomology (A ⊗ E.X₃) r) :
    (tateLeftIso A E.X₁ (r + 1)).hom.hom ((tδ hAE r (r + 1) rfl).hom z) =
      -(tδ (shortExact_tensorLeft_tensor hE A (augIdeal k G) hAE) (r + 1) (r + 1 + 1) rfl).hom
        ((tateLeftIso A E.X₃ r).hom.hom z) := by sorry

alias «GroundTheory».«GroupCoh».«tateLeftIso_tδ'» := P2M_GroundTheory_GroupCoh_tateLeftIso_t___8e34a8e92af3
