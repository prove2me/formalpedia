-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh_t__apply_6f30be77357f
-- name    : P2M_GroundTheory_GroupCoh_t__apply_6f30be77357f
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:55:38.858653+00:00
-- url     : https://prove2.me/theorems/5989bd34-034b-4f73-b85a-abb277ca1d72
-- title:
--   P2 M Ground Theory Group Coh t  apply 6f30be77357f: P2 M Ground Theory Group Coh t  apply 6f30be77357f
-- statement:
--   The P2 M Ground Theory Group Coh t  apply 6f30be77357f construction uses the P2 M Ground Theory Group Coh t  apply 6f30be77357f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateConnecting.lean#L82-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateConnecting.lean#L82-L91

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
set_option backward.isDefEq.respectTransparency false

theorem P2M_GroundTheory_GroupCoh_t__apply_6f30be77357f {S : ShortComplex (Rep k G)} (hS : S.ShortExact) (i : ℤ)
    (x₃ : (tateComplex S.X₃).X i) (hx₃ : ((tateComplex S.X₃).d i (i + 1)).hom x₃ = 0)
    (x₂ : (tateComplex S.X₂).X i) (hx₂ : ((tateComplex.map S.g).f i).hom x₂ = x₃)
    (x₁ : (tateComplex S.X₁).X (i + 1))
    (hx₁ : ((tateComplex.map S.f).f (i + 1)).hom x₁ = ((tateComplex S.X₂).d i (i + 1)).hom x₂)
    (hd : ((tateComplex S.X₁).d (i + 1) (i + 1 + 1)).hom x₁ = 0) :
    (tδ hS i (i + 1) rfl).hom (((tateComplex S.X₃).homologyπ i).hom (tateCyclesMk _ i x₃ hx₃)) =
      ((tateComplex S.X₁).homologyπ (i + 1)).hom (tateCyclesMk _ (i + 1) x₁ hd) := by sorry

alias «GroundTheory».«GroupCoh».«tδ_apply» := P2M_GroundTheory_GroupCoh_t__apply_6f30be77357f
