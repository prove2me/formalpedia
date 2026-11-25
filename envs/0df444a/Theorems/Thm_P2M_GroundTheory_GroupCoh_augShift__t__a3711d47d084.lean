-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh_augShift__t__a3711d47d084
-- name    : P2M_GroundTheory_GroupCoh_augShift__t__a3711d47d084
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:05:01.363374+00:00
-- url     : https://prove2.me/theorems/99fbc604-dc00-5a60-adbb-bebd50f808f2
-- title:
--   P2 M Ground Theory Group Coh aug Shift  t  a3711d47d084: P2 M Ground Theory Group Coh aug Shift  t  a3711d47d084
-- statement:
--   The P2 M Ground Theory Group Coh aug Shift  t  a3711d47d084 construction uses the P2 M Ground Theory Group Coh aug Shift  t  a3711d47d084 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupTateShift.lean#L207-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupTateShift.lean#L207-L216

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

theorem P2M_GroundTheory_GroupCoh_augShift__t__a3711d47d084 (p : ℤ) (a : tateCohomology E.X₃ p) :
    (augShiftδ E.X₁ (p + 1)).hom ((tδ hE p (p + 1) rfl).hom a) =
      -(tδ (shortExact_tensorLeft_of_flat hE (augIdeal k G)) (p + 1) (p + 1 + 1) rfl).hom
        ((augShiftδ E.X₃ p).hom a) := by sorry

alias «GroundTheory».«GroupCoh».«augShiftδ_tδ» := P2M_GroundTheory_GroupCoh_augShift__t__a3711d47d084
