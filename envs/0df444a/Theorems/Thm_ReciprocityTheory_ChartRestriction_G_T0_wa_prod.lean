-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_wa_prod
-- name    : ReciprocityTheory.ChartRestriction.G.T0.wa_prod
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:15:25.621678+00:00
-- url     : https://prove2.me/theorems/9a71507f-dd20-4777-b302-38f4359f4254
-- title:
--   T0: wa prod
-- statement:
--   The T0 construction uses the wa prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/WeakApprox.lean#L64-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/WeakApprox.lean#L64-L75

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_WeakApprox
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open Filter
variable {F : Type*} [Field F]

theorem ReciprocityTheory.ChartRestriction.G.T0.wa_prod {ι : Type*} (w : AddValuation F (WithTop ℤ)) (S : Finset ι) (f : ι → F)
    (e : ι → ℤ) (h : ∀ i ∈ S, w (f i) = e i) :
    w (∏ i ∈ S, f i) = ((∑ i ∈ S, e i : ℤ) : WithTop ℤ) := by sorry
