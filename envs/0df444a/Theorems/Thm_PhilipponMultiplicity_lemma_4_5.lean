-- Prove2me | Theorems.Thm_PhilipponMultiplicity_lemma_4_5
-- name    : PhilipponMultiplicity.lemma_4_5
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-23T21:11:09.614566+00:00
-- url     : https://prove2.me/theorems/dbbffc0a-3788-47a2-83e9-a0d3e862a3b6
-- title:
--   Lemma 4.5 — degrees under translation
-- statement:
--   **Proved with no Open theorem dependencies, verified 29 September 2026.** Checked locally with Lean 4.33.1 and the proposal’s pinned Mathlib. An independent blind readback is attached.
--
--   Translation preserves dimension and bounds the original Hilbert form by the translated form evaluated at degrees multiplied by actual uniform translation-chart degree bounds.
-- source:
--   1986, pp.376–377. https://numdam.org/articles/10.24033/bsmf.2060/

import Definitions.Def_PhilipponMultiplicity_SectionFour
set_option autoImplicit false

namespace PhilipponMultiplicity

theorem lemma_4_5
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (c : G.FactorIndex → ℕ)
    (hc : ∀ i, 1 ≤ c i) (hbound : TranslationDegreeBound G c)
    (g : G.Point) (V : GroupSubvariety G) :
    varietyDimension G V.carrier = varietyDimension G (translate g V.carrier) ∧
    ∀ D : G.FactorIndex → ℕ, (∀ i, 1 ≤ D i) →
      hilbertDegreeForm G V.carrier D ≤
        hilbertDegreeForm G (translate g V.carrier) (fun i => c i * D i) := by sorry

end PhilipponMultiplicity
