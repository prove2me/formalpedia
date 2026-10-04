-- Prove2me | Theorems.Thm_PhilipponMultiplicity_hilbertDegreeForm_scaled_lt_hilbertFunction_univ
-- name    : PhilipponMultiplicity.hilbertDegreeForm_scaled_lt_hilbertFunction_univ
-- status  : Open
-- author  : @junyihjy
-- created : 2026-10-03T20:27:09.490165+00:00
-- url     : https://prove2.me/theorems/a910917c-398c-4dd8-9ed8-e3b4c11e9979
-- title:
--   Scaled Hilbert degree form is strictly below the Hilbert function
-- statement:
--   Decomposition child of PhilipponMultiplicity.addendum_contact_hilbert_gap (05d2413e): the repaired scaled Hilbert bridge replacing the false unscaled bridge H(G;D) ≤ h_{I(G)}(D).
--
--   Let K be a Philippon base field and G an embedded product of commutative algebraic groups of dimension d ≥ 1. For a multidegree D with D_i ≥ H(G;1) (the degree of G) for every factor i, the Hilbert degree form H(G;D), scaled by the reciprocal of the target's hbound constant c = 4^d · d!, is strictly below the Hilbert function of the vanishing ideal of G: (1/c)·H(G;D) < h_{I(G)}(D).
--
--   The constant c is exactly the one in the target's hbound hypothesis, so the assembly chain h_J ≤ C·coset·H(H.carrier) ≤ (1/c)·H(univ) < h_IG closes with a single lt_of_le_of_lt. The unscaled form is false (E×E' counterexample, see addendum_gap_decomposition_spec.md §Child B). Truth evidence: nonvanishing HF(D) ≥ 1; asymptotic HF/P_top → 1 with 4^d slack; curves rigorous via Gruson-Lazarsfeld-Peskine regularity and Castelnuovo genus bound; 25/25 numerical stress checks pass including the original E×E' counterexample. Full proof is a multi-session AG formalization (multigraded regularity + Hilbert-polynomial coefficient bounds), deferred to the prover of this node.
-- source:
--   P. Philippon, Lemmes de zéros dans les groupes algébriques commutatifs, Bull. Soc. Math. France 114 (1986), 355-383; repaired child-B bridge for the converse addendum (see addendum_gap_decomposition_spec.md §Child B). Replaces the false unscaled bridge H(G;D) ≤ h_{I(G)}(D).

import Definitions.Def_PhilipponMultiplicity_Degree
import Definitions.Def_PhilipponMultiplicity_Analytic
set_option autoImplicit false
open scoped BigOperators

namespace PhilipponMultiplicity

theorem hilbertDegreeForm_scaled_lt_hilbertFunction_univ
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (hn : 0 < G.dimension)
    (D : G.FactorIndex → ℕ)
    (hD : ∀ i, hilbertDegreeForm G Set.univ (fun _ => 1) ≤ (D i : ℝ)) :
    (1 / ((4 : ℝ) ^ G.dimension * (G.dimension.factorial : ℝ))) *
        hilbertDegreeForm G Set.univ D <
      (Hilbert.hilbertFunction K G.factorCount G.ambient.ambientDimension
        (G.vanishingIdeal Set.univ) D : ℝ) := by sorry

end PhilipponMultiplicity
