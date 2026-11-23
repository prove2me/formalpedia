-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_JetApproximation_jets
-- name    : ReciprocityTheory.ChartRestriction.G.H1.JetApproximation.jets
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:23:22.305462+00:00
-- url     : https://prove2.me/theorems/8e1ab31e-628c-4065-a2f2-aeb6352149dd
-- title:
--   Jet Approximation: jets
-- statement:
--   The Jet Approximation construction uses the jets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/JetApproximation.lean#L107-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/JetApproximation.lean#L107-L125

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

theorem ReciprocityTheory.ChartRestriction.G.H1.JetApproximation.jets {V : Submodule F R} (h1 : 1 ≤ V) {m : Ideal R} (hm : ∀ x ∈ m, ¬ IsUnit x)
    (hres : ∀ f : R, ∃ c : F, f - algebraMap F R c ∈ m)
    (hfrac : ∀ f : R, ∃ (n : ℕ) (G G' : R), G ∈ V ^ n ∧ G' ∈ V ^ n ∧ IsUnit G' ∧ f * G' = G)
    (D : ℕ) (f : R) : ∃ v ∈ V ^ D, f - v ∈ m ^ (D + 1) := by sorry
