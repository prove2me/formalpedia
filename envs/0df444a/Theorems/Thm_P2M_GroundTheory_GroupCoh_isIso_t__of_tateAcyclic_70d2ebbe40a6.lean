-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh_isIso_t__of_tateAcyclic_70d2ebbe40a6
-- name    : P2M_GroundTheory_GroupCoh_isIso_t__of_tateAcyclic_70d2ebbe40a6
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:37:44.452901+00:00
-- url     : https://prove2.me/theorems/a5ae3f05-6270-4d9d-811d-fa17fa5f4c14
-- title:
--   P2 M Ground Theory Group Coh is Iso t  of tate Acyclic 70d2ebbe40a6: P2 M Ground Theory Group Coh is Iso t  of tate Acyclic 70d2ebbe40a6
-- statement:
--   The P2 M Ground Theory Group Coh is Iso t  of tate Acyclic 70d2ebbe40a6 construction uses the P2 M Ground Theory Group Coh is Iso t  of tate Acyclic 70d2ebbe40a6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/AugmentationSES.lean#L358-L361
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/AugmentationSES.lean#L358-L361

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_InducedNorm
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Definitions.Def_GroundTheory_TateCohomology_TateConnecting
import Definitions.Def_GroundTheory_TateCohomology_AugmentationSES
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory MonoidalCategory
open GroundTheory GroundTheory.GroupCoh
universe u
variable {k G : Type u} [CommRing k] [Group G]
variable (k G)
variable {k G}
variable (k G)
variable {k G}
variable [Fintype G]

theorem P2M_GroundTheory_GroupCoh_isIso_t__of_tateAcyclic_70d2ebbe40a6 {S : ShortComplex (Rep.{u} k G)} (hS : S.ShortExact)
    (h : TateAcyclic S.X₂) (i j : ℤ) (hij : i + 1 = j) : IsIso (tδ hS i j hij) := by sorry

alias «GroundTheory».«GroupCoh».«isIso_tδ_of_tateAcyclic» := P2M_GroundTheory_GroupCoh_isIso_t__of_tateAcyclic_70d2ebbe40a6
