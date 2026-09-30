-- Prove2me | Theorems.Thm_PhilipponMultiplicity_translated_degree_bound_nonnegative
-- name    : PhilipponMultiplicity.translated_degree_bound_nonnegative
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-29T10:00:57.150449+00:00
-- url     : https://prove2.me/theorems/8c308f91-323e-4f07-aae5-4bf1862e4200
-- title:
--   Lemma 4.5 — degree comparison including zero multidegrees
-- statement:
--   Under the hypotheses of Lemma 4.5, for every locally closed group subvariety $V$, every translation $g$, and every natural multidegree $D$, including zero coordinates,
--
--   $$\mathcal H(V;D)\leq\mathcal H(g+V;cD).$$
--
--   The degree forms are the actual top homogeneous parts of the multigraded Hilbert polynomials. This extends the positive-multidegree comparison to the boundary by homogeneity and continuity; it introduces no extra positivity hypothesis into Section 5.
-- source:
--   Patrice Philippon, Lemmes de zéros dans les groupes algébriques commutatifs, Bull. Soc. Math. France 114 (1986), proof of Theorem 2.1 and Lemma 5.1, printed pp. 381–382. https://numdam.org/articles/10.24033/bsmf.2060/

import Definitions.Def_PhilipponMultiplicity_SectionFive
import Definitions.Def_PhilipponMultiplicity_SectionFour
set_option autoImplicit false
open scoped BigOperators

namespace PhilipponMultiplicity

theorem translated_degree_bound_nonnegative
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (c : G.FactorIndex → ℕ)
    (hc : ∀ i, 1 ≤ c i) (hbound : TranslationDegreeBound G c)
    (g : G.Point) (V : GroupSubvariety G) (D : G.FactorIndex → ℕ) :
    hilbertDegreeForm G V.carrier D ≤
      hilbertDegreeForm G (translate g V.carrier) (fun i => c i * D i) := by sorry

end PhilipponMultiplicity
