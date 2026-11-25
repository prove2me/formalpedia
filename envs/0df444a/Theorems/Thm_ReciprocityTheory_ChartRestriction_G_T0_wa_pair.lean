-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_wa_pair
-- name    : ReciprocityTheory.ChartRestriction.G.T0.wa_pair
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:39:24.234138+00:00
-- url     : https://prove2.me/theorems/951a64a4-1753-5632-9be5-bc1b0635ca49
-- title:
--   T0: wa pair
-- statement:
--   The T0 construction uses the wa pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/WeakApprox.lean#L144-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/WeakApprox.lean#L144-L149

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

theorem ReciprocityTheory.ChartRestriction.G.T0.wa_pair (v w : AddValuation F (WithTop ℤ)) (hv : ∀ a : F, a ≠ 0 → v a ≠ ⊤)
    (hw : ∀ a : F, a ≠ 0 → w a ≠ ⊤) (hv1 : ∃ π : F, v π = 1) (hw1 : ∃ ρ : F, w ρ = 1)
    (hne : v ≠ w) : ∃ s, 0 < v s ∧ w s < 0 := by sorry
