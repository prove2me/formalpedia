-- Prove2me | Theorems.Thm_PhilipponMultiplicity_normalized_principal_chart_domain_and_dimension
-- name    : PhilipponMultiplicity.normalized_principal_chart_domain_and_dimension
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-08T07:39:18.691352+00:00
-- url     : https://prove2.me/theorems/755cbb9e-0d8f-4938-a70c-ff925e0cc9ba
-- title:
--   Domain and dimension of a nonempty normalized principal chart
-- statement:
--   Let $K$ satisfy the mission's Philippon base-field hypotheses, let $M=\prod_i\mathbf P^{N_i}_K$, and let $W\subset M$ be a closed irreducible locus. Write $R=K[x_{i,t}]$ for the multihomogeneous coordinate polynomial ring and $I(W)$ for the mission's homogeneous vanishing ideal. Choose an index $b_i\in\{0,\ldots,N_i\}$ for each factor and any polynomial $H\in R$.
--
--   Form the explicit normalized principal chart ring
--   $$
--   A=R[z]\Big/\Big(I(W),\ x_{i,b_i}-1\text{ for all }i,\ H z-1\Big).
--   $$
--   If $A$ is nonzero, then
--   $$
--   A\text{ is an integral domain},\qquad \dim A=\dim W.
--   $$
--
--   Here the left-hand dimension is Krull dimension and the dimension of $W$ is the mission's original geometric dimension defined through its Hilbert polynomial. The quotient uses the displayed ideal itself. The assertion applies to every chosen chart and every $H$ for which the quotient is nonzero, including zero-dimensional $W$.
--
--   This theorem identifies the geometric base of a universal mixed incidence family. Its statement involves no incidence rows, coefficient parameters, or unspecified presentation ring.
--
--   The checked reduction identifies this ring with the localization at the class of $H$ of
--   $$
--   S=R/(I(W),\ x_{i,b_i}-1:i).
--   $$
--   It derives the nonzero denominator from the inverse equation and proves that a nonzero principal localization of an affine domain preserves its domain property and dimension. The outstanding input is [domain and dimension of the normalized affine chart $S$](p2m:theorem/08a4a575-be10-49b5-8fb3-de32eef02dbb), whose statement has no $H$ and no inverse variable.
-- source:
--   Geometric auxiliary for P. Philippon, “Lemmes de zéros dans les groupes algébriques commutatifs”, Bulletin de la Société Mathématique de France 114 (1986), 355–383, §3: dimension and Hilbert-polynomial conventions, Lemma 3.1 (p. 363), and the mixed-linear-section paragraph (p. 364). https://numdam.org/articles/10.24033/bsmf.2060/ . This explicit normalized-chart formulation is a formalization auxiliary, not a verbatim numbered theorem of the paper. Compare Stacks Project, Lemma 10.116.1 (tag 00P0), https://stacks.math.columbia.edu/tag/00P0 , for Krull dimension of a finite type domain over a field, and Lemma 10.114.5 (tag 00OT), https://stacks.math.columbia.edu/tag/00OT , for dimension of nonempty open subsets of affine schemes over a field. The conclusion must still be connected to the mission's actual homogeneous vanishing ideal and Hilbert-polynomial dimension.

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

theorem normalized_principal_chart_domain_and_dimension
    (K : Type u) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K) :
    ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1),
      ∀ H : M.CoordinateRing,
        let A := (Polynomial M.CoordinateRing) ⧸
          (((M.vanishingIdeal W ⊔ Ideal.span (Set.range (fun i : M.FactorIndex =>
            (MvPolynomial.X (⟨i,b i⟩ : M.Variable) : M.CoordinateRing) - 1))).map
              Polynomial.C) ⊔ Ideal.span {Polynomial.C H * Polynomial.X - 1})
        Nontrivial A → IsDomain A ∧ ringKrullDim A = locusDimension M W := by sorry

end PhilipponMultiplicity
