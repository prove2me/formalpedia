-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh_tateCup___left_7b2ba62b5fc0
-- name    : P2M_GroundTheory_GroupCoh_tateCup___left_7b2ba62b5fc0
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:52:17.154516+00:00
-- url     : https://prove2.me/theorems/02490bd6-04e1-56cb-9045-0eec8d55879d
-- title:
--   P2 M Ground Theory Group Coh tate Cup   left 7b2ba62b5fc0: P2 M Ground Theory Group Coh tate Cup   left 7b2ba62b5fc0
-- statement:
--   The P2 M Ground Theory Group Coh tate Cup   left 7b2ba62b5fc0 construction uses the P2 M Ground Theory Group Coh tate Cup   left 7b2ba62b5fc0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupTate.lean#L149-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupTate.lean#L149-L154

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

theorem P2M_GroundTheory_GroupCoh_tateCup___left_7b2ba62b5fc0 {E : ShortComplex (Rep.{u} k G)} (hE : E.ShortExact) (B : Rep.{u} k G)
    (hEB : (E.map (tensorRight B)).ShortExact) (p q r : ℤ) (h : p + q = r)
    (a : tateCohomology E.X₃ p) (b : tateCohomology B q) :
    (TateCohomology.δ hEB r).hom (tateCup p q E.X₃ B r h a b) =
      tateCup (p + 1) q E.X₁ B (r + 1) (by omega) ((TateCohomology.δ hE p).hom a) b := by sorry

alias «GroundTheory».«GroupCoh».«tateCup_δ_left» := P2M_GroundTheory_GroupCoh_tateCup___left_7b2ba62b5fc0
