-- Prove2me | Theorems.Thm_PhilipponMultiplicity_subgroup_hilbert_upper_at_double_degree
-- name    : PhilipponMultiplicity.subgroup_hilbert_upper_at_double_degree
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-10T18:46:16.657984+00:00
-- url     : https://prove2.me/theorems/38880b96-c858-4eab-a6dd-86b19da436b9
-- title:
--   Upper Hilbert bound for an algebraic subgroup at twice the multidegree
-- statement:
--   Let G be a product of embedded commutative algebraic groups over an algebraically closed, complete nontrivially normed field of characteristic zero, and let H be an algebraic subgroup. Write r for the dimension of H, h_H for its actual multigraded Hilbert function, and H(H;D) for the normalized top Hilbert degree form. For every multidegree with positive entries,
--
--   $$h_H(2D)\leq\binom{r+2}{r}H(H;D).$$
--
--   Neither G nor H is required to be connected. The ordinary Chardin bound at degree two gives this inequality after the positive-multidegree Segre–Veronese embedding; the projective closure of a subgroup is reduced and equidimensional. This is the subgroup upper estimate used in the corrected Philippon converse.
--
--   **Formalization status, 10 October 2026:** Proved, with ACCEPTED submission `07198c4c-ea10-4c9a-89b8-b4a5319c40b5`. The proof reuses eight Proved inputs and has no Open dependencies. It constructs finite linear normalization, homogeneous norm polynomials and formal branches to prove the sharp ordinary Hilbert upper bound in characteristic zero, then applies the checked Segre–Veronese and component reductions. The existing base-field hypothesis already supplies characteristic zero. Disconnected subgroups are included; the formal statement is unchanged.
-- source:
--   Derived multigraded specialization for the corrected Philippon erratum converse. Martin Sombra, Bounds for the Hilbert Function of Polynomial Ideals and for the Degrees in the Nullstellensatz, https://arxiv.org/pdf/alg-geom/9610006, introduction p. 3 (Nesterenko lower and Chardin upper estimates), and Theorem 2.4 for the lower bound. The displayed product and Segre–Veronese specializations are derived statements, not quotations.

import Definitions.Def_PhilipponMultiplicity_ErratumCorrections

set_option autoImplicit false
open scoped BigOperators

namespace PhilipponMultiplicity

/-- The Chardin upper bound after the positive-multidegree Segre-Veronese
embedding. The algebraic subgroup may be disconnected. This target is open. -/
theorem subgroup_hilbert_upper_at_double_degree
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (G : EmbeddedGroupProduct K) (H : AlgebraicSubgroup G)
    (D : G.FactorIndex → ℕ) (hD : ∀ i, 1 ≤ D i) :
    (Hilbert.hilbertFunction K G.factorCount G.ambient.ambientDimension
        (G.vanishingIdeal H.carrier) (fun i => 2 * D i) : ℝ) ≤
      (Nat.choose (varietyDimension G H.carrier + 2) (varietyDimension G H.carrier) : ℝ) *
        hilbertDegreeForm G H.carrier D := by sorry

end PhilipponMultiplicity
