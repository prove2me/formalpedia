-- Prove2me | Theorems.Thm_PhilipponMultiplicity_normalized_affine_chart_dimension
-- name    : PhilipponMultiplicity.normalized_affine_chart_dimension
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-08T10:23:55.161129+00:00
-- url     : https://prove2.me/theorems/76ac6e5c-03c4-4aa5-9c47-83e3123d029e
-- title:
--   Krull dimension of a normalized affine chart equals its Hilbert dimension
-- statement:
--   Let $K$ satisfy the mission's Philippon base-field hypotheses, let $M=\prod_i\mathbf P^{N_i}_K$, and let $W\subset M$ be a closed irreducible locus. Write $R=K[x_{i,t}]$ for the multihomogeneous coordinate polynomial ring and $I(W)$ for its homogeneous vanishing ideal. Choose one pivot index $b_i$ in each block and form
--   $$S=R/(I(W),\ x_{i,b_i}-1\text{ for all }i).$$
--   If this quotient is nonzero, then
--   $$\dim S=\dim W.$$
--   Here the left side is Krull dimension of the displayed quotient, and the right side is the total degree of the mission's actual multigraded Hilbert polynomial. The statement covers every pivot choice yielding a nonzero quotient and includes zero-dimensional loci.
--
--   This dimension comparison identifies the normalized affine chart used in the universal mixed-incidence construction. Together with the chart-domain theorem, it supplies the geometric base ring required by the incidence presentation.
--
--   Formalization note: the direct proof has zero Open theorem inputs. It identifies fixed homogeneous quotient pieces under normalization and sandwiches the chart's degree filtration between diagonal Hilbert pieces. The completed Hilbert-polynomial theorem and the explicit Noether-normalization growth theorem then give equal growth exponents. The original formal statement is unchanged.
-- source:
--   Normalized affine-chart dimension auxiliary for P. Philippon, “Lemmes de zéros dans les groupes algébriques commutatifs”, Bulletin de la Société Mathématique de France 114 (1986), 355–383, §3, p. 362 (Hilbert-polynomial degree and geometric dimension) and p. 364 (mixed linear sections). https://numdam.org/articles/10.24033/bsmf.2060/ . The explicit normalization-ideal formulation is a formalization auxiliary, not a verbatim numbered result. Stacks Project Lemma 10.116.1 (00P0), https://stacks.math.columbia.edu/tag/00P0 , gives dimension equal to transcendence degree for an affine integral domain; the comparison with the mission's multigraded Hilbert-polynomial dimension is still part of this child's proof obligation.

import Mathlib
import Definitions.Def_PhilipponMultiplicity_UniversalMixedSlices
import Definitions.Def_PhilipponMultiplicity_GeometricSupport
import Definitions.Def_PhilipponMultiplicity_MixedFlagParameters
set_option autoImplicit false
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.algebraMvPolynomial
universe u

namespace PhilipponMultiplicity
open SectionThree SectionThreeSupport

theorem normalized_affine_chart_dimension
    (K : Type u) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K) :
    ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1),
        let S := M.CoordinateRing ⧸
          (M.vanishingIdeal W ⊔ Ideal.span (Set.range (fun i : M.FactorIndex =>
            (MvPolynomial.X (⟨i,b i⟩ : M.Variable) : M.CoordinateRing) - 1)))
        Nontrivial S → ringKrullDim S = locusDimension M W := by sorry

end PhilipponMultiplicity
