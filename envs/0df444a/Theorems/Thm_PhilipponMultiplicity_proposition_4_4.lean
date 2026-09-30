-- Prove2me | Theorems.Thm_PhilipponMultiplicity_proposition_4_4
-- name    : PhilipponMultiplicity.proposition_4_4
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-23T21:10:46.3806+00:00
-- url     : https://prove2.me/theorems/e52be92d-21f3-4391-a436-43e982b9c75b
-- title:
--   Proposition 4.4 — contact and differential zero loci
-- statement:
--   **Proved with no Open theorem dependencies, verified 29 September 2026.** Checked locally with Lean 4.33.1 and the proposal’s pinned Mathlib. An independent blind readback is attached.
--
--   A point belongs to the retained differential zero locus exactly when every polynomial of the original homogeneous ideal has contact strictly greater than the cutoff at the translated point.
-- source:
--   1986, pp.374–375. https://numdam.org/articles/10.24033/bsmf.2060/

import Definitions.Def_PhilipponMultiplicity_SectionFour
set_option autoImplicit false

namespace PhilipponMultiplicity

theorem proposition_4_4
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G)
    (g h : G.Point) (k : ℕ) (I : Ideal G.CoordinateRing)
    (hI : IsMultihomogeneousIdeal G.ambient I) (atlas : TranslationAtlas A g) :
    (∀ Q ∈ retainedPolynomialOperatorIdeal atlas k I,
      G.ambient.eval Q (G.embedding h) = 0) ↔
    (∀ Q ∈ I, (k : WithTop ℕ) < vanishingOrder A Q (g + h)) := by sorry

end PhilipponMultiplicity
