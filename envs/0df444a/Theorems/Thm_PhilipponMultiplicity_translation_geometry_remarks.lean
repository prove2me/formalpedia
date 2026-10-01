-- Prove2me | Theorems.Thm_PhilipponMultiplicity_translation_geometry_remarks
-- name    : PhilipponMultiplicity.translation_geometry_remarks
-- status  : Open
-- author  : @tomasz
-- created : 2026-09-23T21:12:21.460563+00:00
-- url     : https://prove2.me/theorems/9d66849f-fc9b-4f1c-b13f-593cc377cf81
-- title:
--   Section 4 — translated ideals and embedding remarks
-- statement:
--   **A verified proof-sketch proves the defining-ideal transport clause and reduces the remaining assertions to two explicit Open dependencies: degree invariance under extendable translations and Lange’s quadratic reembedding theorem.** Checked locally with Lean 4.33.1 and the proposal’s pinned Mathlib. An independent blind readback is attached.
--
--   Translate the defining ideal of V to that of V−g. In the connected setting, require Hilbert-form invariance when all translations extend to the projective closure, and a regular reembedding with quadratic translation families as in Lange. Connectedness is explicit; it is necessary for the invariance remark and matches the cited Lange scope.
-- source:
--   1986, pp.358,375–376. https://numdam.org/articles/10.24033/bsmf.2060/

import Definitions.Def_PhilipponMultiplicity_Support
set_option autoImplicit false
open scoped BigOperators Topology

namespace PhilipponMultiplicity

theorem translation_geometry_remarks
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K) :
    (∀ (G : EmbeddedGroupProduct K) (V : GroupSubvariety G) (g : G.Point),
      translatedIdeal G g (G.vanishingIdeal V.carrier) =
        G.vanishingIdeal (translate (-g) V.carrier)) ∧
    (∀ (G : EmbeddedGroupProduct K), @_root_.IsConnected _ G.zariskiTopology Set.univ →
      TranslationsExtendToClosure G →
      ∀ (V : GroupSubvariety G) (g : G.Point) (D : G.FactorIndex → ℕ),
        (∀ i, 1 ≤ D i) →
        hilbertDegreeForm G V.carrier D = hilbertDegreeForm G (translate g V.carrier) D) ∧
    (∀ E : EmbeddedCommutativeGroup K,
      @_root_.IsConnected _ (singleGroupProduct E).zariskiTopology Set.univ →
      ∃ F : EmbeddedCommutativeGroup K, Nonempty (AlgebraicReembedding E F) ∧
        ∀ (A : AnalyticSubgroup (singleGroupProduct F)) (g : (singleGroupProduct F).Point),
          ∃ atlas : TranslationAtlas A g, atlas.IsBoundedBy (fun _ => 2)) := by sorry

end PhilipponMultiplicity
