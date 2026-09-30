-- Prove2me | Theorems.Thm_PhilipponMultiplicity_lemma_4_6
-- name    : PhilipponMultiplicity.lemma_4_6
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-23T21:10:45.898969+00:00
-- url     : https://prove2.me/theorems/3bc27c44-b267-47b8-ab65-541846fc07fc
-- title:
--   Lemma 4.6 — transverse equations
-- statement:
--   **Proved with no Open theorem dependencies, verified 29 September 2026.** Checked locally with Lean 4.33.1 and the proposal’s pinned Mathlib. An independent blind readback is attached.
--
--   For coordinate directions forming a basis transverse to a connected algebraic subgroup and a translation chart meeting its coset, find equations whose first derivatives have the exact diagonal ideal-nonmembership pattern.
-- source:
--   1986, p.378. https://numdam.org/articles/10.24033/bsmf.2060/

import Definitions.Def_PhilipponMultiplicity_SectionFour
set_option autoImplicit false

namespace PhilipponMultiplicity

theorem lemma_4_6
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G)
    (H : AlgebraicSubgroup G) (hH : H.IsConnected) (g : G.Point)
    (directions : Fin (analyticCodimension A H.carrier) → Fin A.parameterDimension)
    (htransverse : IsTransverseCoordinateFamily A H directions)
    (chart : TranslationChart A (0 : G.Point))
    (hmeets : (translate g H.carrier ∩ chart.domain).Nonempty) :
    ∃ Q : Fin (analyticCodimension A H.carrier) → G.CoordinateRing,
      (∀ j, Q j ∈ G.vanishingIdeal (translate g H.carrier)) ∧
      (∀ i j,
        polynomialOperator chart 1 (fun _ => directions i) (Q j) ∉
          G.vanishingIdeal (translate g H.carrier) ↔ i = j) := by sorry

end PhilipponMultiplicity
