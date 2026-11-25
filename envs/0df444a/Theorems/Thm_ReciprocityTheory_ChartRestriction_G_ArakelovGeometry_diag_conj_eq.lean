-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_diag_conj_eq
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.diag_conj_eq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T16:01:28.247903+00:00
-- url     : https://prove2.me/theorems/fb80d8b2-6140-463e-8722-a9fdb9ff5918
-- title:
--   Arakelov Geometry: diag conj eq
-- statement:
--   The Arakelov Geometry construction uses the diag conj eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/CSandwichStE.lean#L61-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/CSandwichStE.lean#L61-L69

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStD
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStE
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

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.diag_conj_eq {r s : ℕ} (N : Matrix (Fin s) (Fin r) ℂ) (G : Matrix (Fin s) (Fin s) ℂ)
    (i : Fin r) :
    (Nᴴ * G * N) i i = star (N *ᵥ Pi.single i 1) ⬝ᵥ G *ᵥ (N *ᵥ Pi.single i 1) := by sorry
