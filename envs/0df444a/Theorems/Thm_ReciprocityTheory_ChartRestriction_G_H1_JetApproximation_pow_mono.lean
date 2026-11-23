-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_JetApproximation_pow_mono
-- name    : ReciprocityTheory.ChartRestriction.G.H1.JetApproximation.pow_mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:02:10.175788+00:00
-- url     : https://prove2.me/theorems/b3ac9d4b-8b54-4cf2-bdc5-84d808f10a23
-- title:
--   Jet Approximation: pow mono
-- statement:
--   The Jet Approximation construction uses the pow mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/JetApproximation.lean#L22-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/JetApproximation.lean#L22-L26

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

theorem ReciprocityTheory.ChartRestriction.G.H1.JetApproximation.pow_mono {V : Submodule F R} (h1 : 1 ≤ V) {a b : ℕ} (hab : a ≤ b) : V ^ a ≤ V ^ b := by sorry
