-- Prove2me | Theorems.Thm_PhilipponMultiplicity_connected_ambient_hilbert_lower
-- name    : PhilipponMultiplicity.connected_ambient_hilbert_lower
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-10T18:47:23.95202+00:00
-- url     : https://prove2.me/theorems/99ae1e93-4cfa-4b02-919b-c2a4fbffe50f
-- title:
--   Lower Hilbert bound for the connected ambient product
-- statement:
--   Let G be a connected product of embedded commutative algebraic groups over an algebraically closed, complete nontrivially normed field of characteristic zero. Write n for its dimension, h_G for its actual multigraded Hilbert function, and H(G;D) for the normalized top Hilbert degree form. If every entry of the multidegree D is at least H(G;1), then
--
--   $$h_G(D)\geq\frac{H(G;D)}{2^n n!}.$$
--
--   The multidegree 1 has every entry equal to one. No bound on the addition laws is required for this Hilbert estimate. It is the ambient lower estimate in the corrected Philippon converse, derived mathematically from the ordinary Nesterenko lower bound factor by factor and the product Hilbert formula.
-- source:
--   Derived multigraded specialization for the corrected Philippon erratum converse. Martin Sombra, Bounds for the Hilbert Function of Polynomial Ideals and for the Degrees in the Nullstellensatz, https://arxiv.org/pdf/alg-geom/9610006, introduction p. 3 (Nesterenko lower and Chardin upper estimates), and Theorem 2.4 for the lower bound. The displayed product and Segre–Veronese specializations are derived statements, not quotations.

import Definitions.Def_PhilipponMultiplicity_ErratumCorrections

set_option autoImplicit false
open scoped BigOperators

namespace PhilipponMultiplicity

/-- The product version of the lower Hilbert-function estimate, at the
degree threshold used in the corrected converse. This target remains open. -/
theorem connected_ambient_hilbert_lower
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (hG : G.IsConnected)
    (D : G.FactorIndex → ℕ)
    (hD : ∀ i, hilbertDegreeForm G Set.univ (fun _ => 1) ≤ (D i : ℝ)) :
    hilbertDegreeForm G Set.univ D /
        ((2 : ℝ) ^ G.dimension * (G.dimension.factorial : ℝ)) ≤
      (Hilbert.hilbertFunction K G.factorCount G.ambient.ambientDimension
        (G.vanishingIdeal Set.univ) D : ℝ) := by sorry

end PhilipponMultiplicity
