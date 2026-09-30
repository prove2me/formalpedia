-- Prove2me | Theorems.Thm_PhilipponMultiplicity_differentialIdeal_eq_local_polynomial_jet_ideal
-- name    : PhilipponMultiplicity.differentialIdeal_eq_local_polynomial_jet_ideal
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-27T18:42:17.367645+00:00
-- url     : https://prove2.me/theorems/7e8afc8d-18d3-4fdb-991f-8f915ecd98b0
-- title:
--   Local normalized analytic jets and polynomial jet sections generate the same ideal
-- statement:
--   For a permitted base field, analytic subgroup, translation point, supplied genuine polynomial translation atlas, derivative bound $T$, and multihomogeneous ideal $I$, the intrinsic normalized analytic jets and the normalized polynomial sections of the polynomial-operator ideal generate the same local ideal. Both sides use the existing Zariski-local rational-coefficient definition. This is the finite Leibniz and projective-pivot change of generators in Proposition 4.3, before converting local generation into primary-component retention. The statement is an explicit unproved analytic dependency; the algebraic retention/local-generation conversion is a separate completed theorem.
-- source:
--   Philippon (1986), Lemmes de zéros dans les groupes algébriques commutatifs, Definition 4.2 and Proposition 4.3, printed pp. 373–374; https://numdam.org/articles/10.24033/bsmf.2060/ .

import Definitions.Def_PhilipponMultiplicity_SectionFour
import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport
set_option autoImplicit false
open scoped BigOperators Topology
open PhilipponMultiplicity

theorem PhilipponMultiplicity.differentialIdeal_eq_local_polynomial_jet_ideal
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (A : AnalyticSubgroup G) (g : G.Point)
    (atlas : TranslationAtlas A g) (T : ℕ) (I : Ideal G.CoordinateRing)
    (hI : IsMultihomogeneousIdeal G.ambient I) :
    differentialIdeal A g T I = translatedIdeal G 0 (polynomialOperatorIdeal atlas T I) := by sorry
