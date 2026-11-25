-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_A_chord_to_convex
-- name    : ReciprocityTheory.AnForm.A.chord_to_convex
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:51:00.852222+00:00
-- url     : https://prove2.me/theorems/2363fb26-b643-4003-bddf-001a6ebd1efe
-- title:
--   A: chord to convex
-- statement:
--   The A construction uses the chord to convex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshMoll.lean#L81-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PlurisubharmonicFunctions/PshMoll.lean#L81-L105

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMollB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMoll
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Metric Filter Topology Set
noncomputable section
variable {D : ℕ}

theorem ReciprocityTheory.AnForm.A.chord_to_convex {f : ℝ → ℝ} {s : Set ℝ} (hs : Convex ℝ s)
    (h : ∀ x ∈ s, ∀ y ∈ s, x < y → ∀ α β : ℝ, f x ≤ α + β * x → f y ≤ α + β * y →
      ∀ p ∈ Icc x y, f p ≤ α + β * p) : ConvexOn ℝ s f := by sorry
