-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_eval_prodForm
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.eval_prodForm
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T15:47:57.386867+00:00
-- url     : https://prove2.me/theorems/e1920294-2e7b-41ea-8cae-9ac6b8caa43f
-- title:
--   Arakelov Geometry: eval prod Form
-- statement:
--   The Arakelov Geometry construction uses the eval prod Form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/CSandwichStD.lean#L184-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/CSandwichStD.lean#L184-L189

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder Matrix
variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.eval_prodForm (e : Fin (D + 1) → Ix κ) (a : Fin (D + 1) → ℕ) (h : MvPolynomial (Ix κ) ℤ)
    (z : Ix κ → ℂ) :
    eval z (map (Int.castRingHom ℂ) (prodForm e a h)) =
      monoC a (z ∘ e) * eval z (map (Int.castRingHom ℂ) h) := by sorry
