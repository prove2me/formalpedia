-- Prove2me | Theorems.Thm_P2M_GroundTheory_GroupCoh_tateCup___right_e29a4e04fc7a
-- name    : P2M_GroundTheory_GroupCoh_tateCup___right_e29a4e04fc7a
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:06:11.561653+00:00
-- url     : https://prove2.me/theorems/14e654d2-1ea5-46cb-8a1b-d14d72463be4
-- title:
--   P2 M Ground Theory Group Coh tate Cup   right e29a4e04fc7a: P2 M Ground Theory Group Coh tate Cup   right e29a4e04fc7a
-- statement:
--   The P2 M Ground Theory Group Coh tate Cup   right e29a4e04fc7a construction uses the P2 M Ground Theory Group Coh tate Cup   right e29a4e04fc7a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupTate.lean#L156-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupTate.lean#L156-L162

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

theorem P2M_GroundTheory_GroupCoh_tateCup___right_e29a4e04fc7a {E : ShortComplex (Rep.{u} k G)} (hE : E.ShortExact) (A : Rep.{u} k G)
    (hAE : (E.map (tensorLeft A)).ShortExact) (p q r : ℤ) (h : p + q = r)
    (a : tateCohomology A p) (b : tateCohomology E.X₃ q) :
    (TateCohomology.δ hAE r).hom (tateCup p q A E.X₃ r h a b) =
      p.negOnePow • tateCup p (q + 1) A E.X₁ (r + 1) (by omega) a ((TateCohomology.δ hE q).hom b) := by sorry

alias «GroundTheory».«GroupCoh».«tateCup_δ_right» := P2M_GroundTheory_GroupCoh_tateCup___right_e29a4e04fc7a
