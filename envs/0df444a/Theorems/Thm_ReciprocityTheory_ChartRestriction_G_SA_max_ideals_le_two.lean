-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_max_ideals_le_two
-- name    : ReciprocityTheory.ChartRestriction.G.SA.max_ideals_le_two
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:33:51.059923+00:00
-- url     : https://prove2.me/theorems/29b34791-dd37-5b12-9002-04a3913fb186
-- title:
--   SA: max ideals le two
-- statement:
--   The SA construction uses the max ideals le two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/LocGen.lean#L7-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/LocGen.lean#L7-L39

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_SUEqClosure
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_SAOpenStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_LocGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.SA

theorem ReciprocityTheory.ChartRestriction.G.SA.max_ideals_le_two {k K : Type*} [Field k] [CommRing K] [Algebra k K]
    (hrank : Module.finrank k K = 2) (m₀ m₁ m₂ : Ideal K) (h₀ : m₀.IsMaximal) (h₁ : m₁.IsMaximal)
    (h₂ : m₂.IsMaximal) : m₀ = m₁ ∨ m₀ = m₂ ∨ m₁ = m₂ := by sorry
