-- Prove2me | Theorems.Thm_PhilipponMultiplicity_exists_open_preserving_point_local_isolated_equations
-- name    : PhilipponMultiplicity.exists_open_preserving_point_local_isolated_equations
-- status  : Open
-- author  : @tomasz
-- created : 2026-10-07T12:03:02.56229+00:00
-- url     : https://prove2.me/theorems/b3b3c207-d3c1-4690-863e-08a7b53646e9
-- title:
--   Persistence from the local radical ideals of isolated mixed intersections
-- statement:
--   Let $K$ be a Philippon base field, $M=\prod_i\mathbf P^{n_i}$, and $W\subseteq M$ a closed irreducible subset. Choose $0\le\alpha_i\le n_i$ with $\sum_i\alpha_i=\dim W$, where dimension is the total degree of the actual multigraded quotient Hilbert polynomial. Let $l=(i_0,\ldots,i_{s-1})$ list each block $i$ exactly $\alpha_i$ times.
--
--   For a coefficient array $c$, put
--   $$
--   P_j(c)=\sum_{t=0}^{n_{i_j}}c_{j,(i_j,t)}X_{i_j,t},\quad
--   J(c)=I(W)+(P_0(c),\ldots,P_{s-1}(c)),\quad
--   Z(c)=\{x\in W:P_j(c)(x)=0\text{ for every }j\}.
--   $$
--   Choose initial coefficients $c^0$ and a finite subset $S\subseteq Z(c^0)$. Write $A=K[X_{i,t}]$. Assume that every $x\in S$ has the following local algebra property: for every coordinate tuple $v$ with all blocks nonzero and representing $x$, the radical of the localized equation ideal is precisely the localized ideal of the point cone:
--   $$
--   \sqrt{J(c^0)A_{\mathfrak m_v}}=I(\{x\})A_{\mathfrak m_v},
--   \qquad \mathfrak m_v=\ker(A\xrightarrow{\operatorname{ev}_v}K).
--   $$
--   Here $I(\{x\})$ is the multihomogeneous vanishing ideal of the projective point, so independent scaling directions in its coordinate blocks remain. The equality does not require $J(c^0)A_{\mathfrak m_v}$ itself to be radical.
--
--   Let $C=K[T_{j,w}]$ be the polynomial ring on all coefficient entries and $\mathfrak n_c$ its evaluation maximal ideal. There is a Zariski-open subset $U\subseteq\operatorname{Spec}C$ with
--   $$
--   \mathfrak n_{c^0}\in U,\qquad
--   \mathfrak n_c\in U\ \Longrightarrow\ \text{there is an injection }S\hookrightarrow Z(c).
--   $$
--   Thus the prescribed points persist in number under perturbation of the equations. Positive-dimensional components elsewhere, nonreduced isolated intersections, empty $S$, and empty equation lists are allowed. The injection may choose new points in each fibre.
--
--   **Formalization Note.** This auxiliary statement is not a verbatim numbered source theorem. A checked reduction now proves finite-dimensionality of the normalized local equation algebra at each selected point, retaining nilpotents. One pivot per projective block is set to 1; the point-cone ideal plus these normalization equations is the affine evaluation maximal ideal. The original radical equality then makes the normalized quotient finite over the coefficient field through a finitely generated nilpotent kernel. The sole remaining child is [persistence from finite normalized local algebras](p2m:theorem/15ace125-00ef-4ed1-8f91-53698fcbcc31). Construction and comparison of the mixed incidence scheme, dimension and dominance, and the openness and étale separation argument remain Open. The original formal statement is unchanged.
-- source:
--   P. Philippon, Lemmes de zeros dans les groupes algebriques commutatifs, Bull. SMF 114 (1986), Lemma 3.1 and the mixed-section paragraph, pp.363–364, https://numdam.org/articles/10.24033/bsmf.2060/ . Stacks Project, Lemma 37.41.5 (Tag 02LO), https://stacks.math.columbia.edu/tag/02LO ; Lemma 37.74.2 (Tag 0F32), https://stacks.math.columbia.edu/tag/0F32 ; Lemma 29.29.4 (Tag 02FZ), https://stacks.math.columbia.edu/tag/02FZ . Auxiliary synthesis: translate the concrete point-local radical certificate to isolated fibre points of the mixed incidence scheme, use its dimension and dominance over the regular coefficient space, and combine universal openness on the quasi-finite locus with etale separation of the finitely many points. These geometric steps remain Open. The parent proves the local radical certificate using homogeneous principal opens, finite point separation and the Hilbert Nullstellensatz, Theorem 10.34.1 (Tag 00FV), https://stacks.math.columbia.edu/tag/00FV .

import Mathlib
import Definitions.Def_PhilipponMultiplicity_GeometricSupport
import Definitions.Def_PhilipponMultiplicity_MixedFlagParameters
set_option autoImplicit false
open scoped BigOperators Topology

namespace PhilipponMultiplicity
open SectionThree SectionThreeSupport

theorem exists_open_preserving_point_local_isolated_equations
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K) :
    ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ l : List M.FactorIndex, (∀ i, l.count i = α i) →
      ∀ c₀ : Fin l.length → M.Variable → K,
      ∀ S : Set M.Point, S.Finite →
      S ⊆ {x : M.Point | x ∈ W ∧
        ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c₀ j) x = 0} →
      (∀ x ∈ S, ∀ v : M.Variable → K,
        (∀ i : M.FactorIndex, ∃ h : (fun j => v ⟨i,j⟩) ≠ 0,
          Projectivization.mk K (fun j => v ⟨i,j⟩) h = x i) →
        ((MixedFlag.ideal M (M.vanishingIdeal W) l c₀ l.length).map
          (algebraMap M.CoordinateRing
            (Localization.AtPrime (MvPolynomial.vanishingIdeal K {v})))).radical =
          (M.vanishingIdeal {x}).map (algebraMap M.CoordinateRing
            (Localization.AtPrime (MvPolynomial.vanishingIdeal K {v})))) →
        ∃ U : Set (PrimeSpectrum (MvPolynomial (Fin l.length × M.Variable) K)),
          IsOpen U ∧
          (⟨MvPolynomial.vanishingIdeal K {Function.uncurry c₀}, inferInstance⟩ :
            PrimeSpectrum (MvPolynomial (Fin l.length × M.Variable) K)) ∈ U ∧
          ∀ c : Fin l.length → M.Variable → K,
            (⟨MvPolynomial.vanishingIdeal K {Function.uncurry c}, inferInstance⟩ :
              PrimeSpectrum (MvPolynomial (Fin l.length × M.Variable) K)) ∈ U →
            Nonempty (S ↪ {x : M.Point | x ∈ W ∧
              ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c j) x = 0}) := by sorry

end PhilipponMultiplicity
