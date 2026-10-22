-- Prove2me | Theorems.Thm_SidB_ms_square
-- name    : SidB.ms_square
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-21T21:24:49.583558+00:00
-- url     : https://prove2.me/theorems/2dd1b98a-bc1e-4506-8511-16ba94e4dfa6
-- title:
--   The square of the Moebius ladder dominates the (5,3)-incidence graph (Theorem 2.1)
-- statement:
--   Theorem 2.1 of the paper: for every graphon W, the homomorphism density of the (5,3)-incidence graph F_{5,3} is at most the homomorphism density of the square M^2 of the Moebius ladder M = K_{5,5} minus its ten-cycle, t_{F_{5,3}}(W) <= t_{M^2}(W). The proof writes t_{M^2}(W) as the expectation of the product over the five triples Z_i of rho(x_{Z_i})^2 and t_{F_{5,3}}(W) as the expectation of the product over all ten triples of rho once; symmetrizing over the 5! permutations of the left part and applying Hoelder's inequality (1) in the form E prod_I f~_I <= prod_phi (E prod_I f_{phi(I)})^(1/5!) closes the comparison, since the Z_i constitute half the triples. In the mission the inequality is the statement that the density of incGraph53 is at most the density of mobiusSquare for every graphon.
--
--   **Formalization Note** The symmetrization uses the transport axiom of the graphon interface over the permutations of the five-element left part, and the Hoelder (AM-GM) axiom is exactly the inequality (1) of the paper; the rho-power functionals are the weighted products the axiom consumes.
-- source:
--   D. Conlon, J. Lee, Sidorenko's conjecture for blow-ups, Discrete Anal. 2021:2 (2021), Section 2 (Theorem 2.1, pages 3-4).

import Mathlib
import Definitions.Def_SidB_graph
import Definitions.Def_SidB_hyper

namespace SidB

/-!  Milestone 1 (Theorem 2.1): the square of the Moebius ladder dominates
the (5,3)-incidence graph. For every graphon, the homomorphism density of
the (5,3)-incidence graph F_{5,3} is at most the homomorphism density of
the square M^2 of the Moebius ladder M = K_{5,5} minus its ten-cycle. The
proof of Section 2 symmetrizes over the permutations of the five-element
left part and applies the Hoelder axiom (the AM-GM inequality for the
expectation functional); the weak-norming property of the incidence graph,
recorded in the mission's milestone 4, then lifts this to Sidorenko for
M^2. -/
theorem ms_square (g : Graphon) :
    g.dens incGraph53 ≤ g.dens mobiusSquare := by sorry

end SidB
