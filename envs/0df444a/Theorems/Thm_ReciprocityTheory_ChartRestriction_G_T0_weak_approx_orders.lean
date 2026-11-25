-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_weak_approx_orders
-- name    : ReciprocityTheory.ChartRestriction.G.T0.weak_approx_orders
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:30:31.855978+00:00
-- url     : https://prove2.me/theorems/a0b65198-b6c6-40f5-99fa-3d8b60eb35b1
-- title:
--   T0: weak approx orders
-- statement:
--   The T0 construction uses the weak approx orders property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/WeakApprox.lean#L292-L340
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/WeakApprox.lean#L292-L340

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

theorem ReciprocityTheory.ChartRestriction.G.T0.weak_approx_orders {F : Type*} [Field F] {k : ℕ} (v : Fin k → AddValuation F (WithTop ℤ))
    (hfin : ∀ i (a : F), a ≠ 0 → v i a ≠ ⊤) (hone : ∀ i, ∃ π : F, v i π = 1)
    (hdist : Pairwise fun i j => v i ≠ v j) (n : Fin k → ℤ) :
    ∃ g : F, ∀ i, v i g = n i := by sorry
