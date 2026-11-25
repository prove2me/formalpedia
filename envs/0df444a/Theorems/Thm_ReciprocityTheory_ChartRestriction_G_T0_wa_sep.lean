-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_wa_sep
-- name    : ReciprocityTheory.ChartRestriction.G.T0.wa_sep
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:39:39.11402+00:00
-- url     : https://prove2.me/theorems/003c9c63-027b-44e5-ad9f-28dd1fade277
-- title:
--   T0: wa sep
-- statement:
--   The T0 construction uses the wa sep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/WeakApprox.lean#L181-L274
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/WeakApprox.lean#L181-L274

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

theorem ReciprocityTheory.ChartRestriction.G.T0.wa_sep {ι : Type*} [DecidableEq ι] (v : ι → AddValuation F (WithTop ℤ))
    (hfin : ∀ i (a : F), a ≠ 0 → v i a ≠ ⊤) (hone : ∀ i, ∃ π : F, v i π = 1)
    (hdist : Pairwise fun i j => v i ≠ v j) (i : ι) (T : Finset ι) (hi : i ∉ T) :
    ∃ s : F, s ≠ 0 ∧ 0 < v i s ∧ ∀ j ∈ T, v j s < 0 := by sorry
