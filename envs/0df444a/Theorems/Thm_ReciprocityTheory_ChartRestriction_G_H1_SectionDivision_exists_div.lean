-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_SectionDivision_exists_div
-- name    : ReciprocityTheory.ChartRestriction.G.H1.SectionDivision.exists_div
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:26:43.018972+00:00
-- url     : https://prove2.me/theorems/8cff87f0-f43d-4147-8272-7ee74cf1bfec
-- title:
--   Section Division: exists div
-- statement:
--   The Section Division construction uses the exists div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/SectionDivision.lean#L53-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/SectionDivision.lean#L53-L66

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionDivision
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1 ReciprocityTheory.ChartRestriction.G.H1.SectionDivision
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi

theorem ReciprocityTheory.ChartRestriction.G.H1.SectionDivision.exists_div (hmul : MulNSt) {k : Type} [Field k] [IsAlgClosed k]
    (P : PolAV (Spec (CommRingCat.of k))) (a₀ : baseOver (Spec (CommRingCat.of k)) ⟶ P.A) (r : ℕ)
    (hr : 1 ≤ r) : ∃ b : baseOver (Spec (CommRingCat.of k)) ⟶ P.A, b ^ r = a₀ := by sorry
