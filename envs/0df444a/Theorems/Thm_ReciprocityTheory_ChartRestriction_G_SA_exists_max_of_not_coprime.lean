-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_exists_max_of_not_coprime
-- name    : ReciprocityTheory.ChartRestriction.G.SA.exists_max_of_not_coprime
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:33:19.325811+00:00
-- url     : https://prove2.me/theorems/02c8e6c7-c497-4ccf-b048-6ce31e49acc6
-- title:
--   SA: exists max of not coprime
-- statement:
--   The SA construction uses the exists max of not coprime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/ExistsMaxOfNotCoprime.lean#L47-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/ExistsMaxOfNotCoprime.lean#L47-L57

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_ExistsMaxOfNotCoprime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.SA

theorem ReciprocityTheory.ChartRestriction.G.SA.exists_max_of_not_coprime {K : Type*} [CommRing K] {a b : K} (h : ¬ IsCoprime a b) :
    ∃ m : Ideal K, m.IsMaximal ∧ a ∈ m ∧ b ∈ m := by sorry
