-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh_tateLeftIso_t__34419956ee59
-- name    : P2M_GroundTheory_GroupCoh_tateLeftIso_t__34419956ee59
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:53:56.08482+00:00
-- url     : https://prove2.me/theorems/c61e8ddb-476a-4885-9509-d86547eaaf5d
-- title:
--   P2 M Ground Theory Group Coh tate Left Iso t  34419956ee59: P2 M Ground Theory Group Coh tate Left Iso t  34419956ee59
-- statement:
--   The P2 M Ground Theory Group Coh tate Left Iso t  34419956ee59 construction uses the P2 M Ground Theory Group Coh tate Left Iso t  34419956ee59 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupTateShift.lean#L192-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupTateShift.lean#L192-L203

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

theorem P2M_GroundTheory_GroupCoh_tateLeftIso_t__34419956ee59 (B : Rep.{u} k G) (hEB : (E.map (tensorRight B)).ShortExact) (r : ℤ)
    (z : tateCohomology (E.X₃ ⊗ B) r) :
    (tateLeftIso E.X₁ B (r + 1)).hom.hom ((tδ hEB r (r + 1) rfl).hom z) =
      -(tδ (shortExact_tensorLeft_tensorRight hE B (augIdeal k G) hEB) (r + 1) (r + 1 + 1)
        rfl).hom ((tateLeftIso E.X₃ B r).hom.hom z) := by sorry

alias «GroundTheory».«GroupCoh».«tateLeftIso_tδ» := P2M_GroundTheory_GroupCoh_tateLeftIso_t__34419956ee59
