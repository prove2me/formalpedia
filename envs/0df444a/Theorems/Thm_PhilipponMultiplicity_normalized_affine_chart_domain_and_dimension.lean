-- Prove2me | Theorems.Thm_PhilipponMultiplicity_normalized_affine_chart_domain_and_dimension
-- name    : PhilipponMultiplicity.normalized_affine_chart_domain_and_dimension
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-08T08:57:42.775987+00:00
-- url     : https://prove2.me/theorems/08a4a575-be10-49b5-8fb3-de32eef02dbb
-- title:
--   Domain and dimension of a nonempty normalized affine chart
-- statement:
--   Let $K$ satisfy the mission's Philippon base-field hypotheses, let $M=\prod_i\mathbf P^{N_i}_K$, and let $W\subset M$ be a closed irreducible locus. Write $R=K[x_{i,t}]$ and let $I(W)$ be the mission's homogeneous vanishing ideal. Choose a pivot coordinate $x_{i,b_i}$ in each block and form
--   $$S=R/(I(W),\ x_{i,b_i}-1\text{ for all }i).$$
--   If $S$ is nonzero, then $S$ is an integral domain and its Krull dimension equals the dimension of $W$ defined through the mission's multigraded Hilbert polynomial. The assertion concerns the displayed ideal itself and applies to every allowed pivot choice, including zero-dimensional loci.
--
--   The checked domain proof embeds $S$ into the fraction field of $R/I(W)$ using normalized coordinates. Nontriviality of $S$ forces the pivot classes to be nonzero. Homogeneous scaling and a homogenization identity valid in arbitrary normalized algebras prove that the kernel is exactly the chart ideal. Thus the domain assertion is complete.
--
--   The sole outstanding input is [the Krull/Hilbert dimension comparison for this normalized chart](p2m:theorem/76ac6e5c-03c4-4aa5-9c47-83e3123d029e); its statement has only the dimension conclusion. The original formal target and its hypotheses are unchanged.
-- source:
--   Normalized affine-chart auxiliary for P. Philippon, “Lemmes de zéros dans les groupes algébriques commutatifs”, Bulletin de la Société Mathématique de France 114 (1986), 355–383, §3: geometric/Hilbert-polynomial dimension conventions, Lemma 3.1 on p. 363, and the mixed-linear-section paragraph on p. 364. https://numdam.org/articles/10.24033/bsmf.2060/ . This explicit quotient formulation is a formalization auxiliary, not a verbatim numbered theorem in Philippon. The required affine dimension comparison is consistent with Stacks Project, Lemma 10.116.1 (00P0), https://stacks.math.columbia.edu/tag/00P0 , and the proof of Lemma 10.114.5 (00OT), https://stacks.math.columbia.edu/tag/00OT . The identification of the displayed normalization ideal with the affine chart and the comparison with the mission's actual Hilbert-polynomial dimension are part of this theorem's proof obligation.

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

theorem normalized_affine_chart_domain_and_dimension
    (K : Type u) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K) :
    ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1),
        let S := M.CoordinateRing ⧸
          (M.vanishingIdeal W ⊔ Ideal.span (Set.range (fun i : M.FactorIndex =>
            (MvPolynomial.X (⟨i,b i⟩ : M.Variable) : M.CoordinateRing) - 1)))
        Nontrivial S → IsDomain S ∧ ringKrullDim S = locusDimension M W := by sorry

end PhilipponMultiplicity
