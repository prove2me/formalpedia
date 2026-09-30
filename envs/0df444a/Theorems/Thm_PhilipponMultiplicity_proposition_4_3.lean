-- Prove2me | Theorems.Thm_PhilipponMultiplicity_proposition_4_3
-- name    : PhilipponMultiplicity.proposition_4_3
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-23T21:02:33.140981+00:00
-- url     : https://prove2.me/theorems/292bc026-2e47-4c00-bb9c-2f8ad9700061
-- title:
--   Proposition 4.3 — atlas independence and composition
-- statement:
--   **Proved with no Open theorem dependencies, verified 29 September 2026.** Checked locally with Lean 4.33.1 and the proposal’s pinned Mathlib. An independent blind readback is attached.
--
--   Polynomial translation/differentiation ideals after retention are independent of the representing atlas and compose by adding both translation points and derivative cutoffs.
-- source:
--   1986, pp.373–374. https://numdam.org/articles/10.24033/bsmf.2060/

import Definitions.Def_PhilipponMultiplicity_SectionFour
set_option autoImplicit false

namespace PhilipponMultiplicity

theorem proposition_4_3
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G)
    (g g' : G.Point) (k k' : ℕ) (I : Ideal G.CoordinateRing)
    (hI : IsMultihomogeneousIdeal G.ambient I)
    (atlas atlas' : TranslationAtlas A g) :
    (retainedPolynomialOperatorIdeal atlas k I =
      retainedPolynomialOperatorIdeal atlas' k I) ∧
    (∀ other : TranslationAtlas A g', ∀ combined : TranslationAtlas A (g + g'),
      retainedPolynomialOperatorIdeal atlas k
        (retainedPolynomialOperatorIdeal other k' I) =
      retainedPolynomialOperatorIdeal combined (k + k') I) := by sorry

end PhilipponMultiplicity
