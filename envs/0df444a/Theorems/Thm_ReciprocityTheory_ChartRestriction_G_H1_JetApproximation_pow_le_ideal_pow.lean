-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_JetApproximation_pow_le_ideal_pow
-- name    : ReciprocityTheory.ChartRestriction.G.H1.JetApproximation.pow_le_ideal_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:02:53.733218+00:00
-- url     : https://prove2.me/theorems/e36388a5-6e7c-4b84-8820-5e50955e95de
-- title:
--   Jet Approximation: pow le ideal pow
-- statement:
--   The Jet Approximation construction uses the pow le ideal pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/JetApproximation.lean#L28-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/JetApproximation.lean#L28-L37

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_JetApproximation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1 ReciprocityTheory.ChartRestriction.G.H1.JetApproximation
variable {F R : Type*} [Field F] [CommRing R] [Algebra F R]

theorem ReciprocityTheory.ChartRestriction.G.H1.JetApproximation.pow_le_ideal_pow {W : Submodule F R} {m : Ideal R} (h : W ≤ m.restrictScalars F) :
    ∀ k : ℕ, W ^ k ≤ (m ^ k).restrictScalars F
  := by sorry
