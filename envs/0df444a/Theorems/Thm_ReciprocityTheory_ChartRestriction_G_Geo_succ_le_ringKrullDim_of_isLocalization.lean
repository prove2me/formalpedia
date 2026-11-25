-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_succ_le_ringKrullDim_of_isLocalization
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.succ_le_ringKrullDim_of_isLocalization
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:25:35.697979+00:00
-- url     : https://prove2.me/theorems/5cb410c7-02f5-4972-b71b-e1b6949de129
-- title:
--   Geo: succ le ring Krull Dim of is Localization
-- statement:
--   The Geo construction uses the succ le ring Krull Dim of is Localization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterGoodA.lean#L99-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterGoodA.lean#L99-L119

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open Ideal

theorem ReciprocityTheory.ChartRestriction.G.Geo.succ_le_ringKrullDim_of_isLocalization {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (M : Submonoid A) [IsLocalization M B]
    (hext : ∀ p : Ideal A, p.IsPrime → Disjoint (M : Set A) p → ∃ q : Ideal A, q.IsPrime ∧ p < q)
    (n : ℕ) (h : (n : WithBot ℕ∞) ≤ ringKrullDim B) :
    ((n + 1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim A := by sorry
