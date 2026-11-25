-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh_cupH_zero_zero___5acd48460960
-- name    : P2M_GroundTheory_GroupCoh_cupH_zero_zero___5acd48460960
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T07:53:43.309806+00:00
-- url     : https://prove2.me/theorems/cb2aec32-f451-4e9b-a63b-fcffab075042
-- title:
--   P2 M Ground Theory Group Coh cup H zero zero   5acd48460960: P2 M Ground Theory Group Coh cup H zero zero   5acd48460960
-- statement:
--   The P2 M Ground Theory Group Coh cup H zero zero   5acd48460960 construction uses the P2 M Ground Theory Group Coh cup H zero zero   5acd48460960 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupTate.lean#L21-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupTate.lean#L21-L34

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupTateShift
import Definitions.Def_GroundTheory_TateCohomology_CupTate
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
omit [Fintype G]

theorem P2M_GroundTheory_GroupCoh_cupH_zero_zero___5acd48460960 {A B : Rep.{u} k G} (f : (Fin 0 → G) → A) (g : (Fin 0 → G) → B)
    (hf : (inhomogeneousCochains.d A 0).hom f = 0) (hg : (inhomogeneousCochains.d B 0).hom g = 0)
    (fg : (Fin 0 → G) → (A ⊗ B : Rep k G)) (hfg : (inhomogeneousCochains.d (A ⊗ B) 0).hom fg = 0)
    (h : ∀ v, fg v = f v ⊗ₜ[k] g v) :
    cupH rfl (π A 0 (cocyclesMk f hf)) (π B 0 (cocyclesMk g hg)) = π (A ⊗ B) 0 (cocyclesMk fg hfg) := by sorry

alias «GroundTheory».«GroupCoh».«cupH_zero_zero_π» := P2M_GroundTheory_GroupCoh_cupH_zero_zero___5acd48460960
