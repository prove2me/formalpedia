-- Prove2me | Theorems.Thm_PhilipponMultiplicity_exists_open_preserving_finite_affine_mixed_neighborhoods
-- name    : PhilipponMultiplicity.exists_open_preserving_finite_affine_mixed_neighborhoods
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-07T13:34:15.332499+00:00
-- url     : https://prove2.me/theorems/2eac4ece-8a33-49bc-afda-520b38f3f704
-- title:
--   Persistence of mixed sections from finite principal neighborhoods
-- statement:
--   Let $K$ be a Philippon base field, $M=\prod_i\mathbf P^{n_i}$, and $W\subseteq M$ a closed irreducible subset. Choose integers $0\le\alpha_i\le n_i$ with $\sum_i\alpha_i=\dim W$. Dimension here is the total degree of the actual multigraded quotient Hilbert polynomial. Let $l=(i_0,\ldots,i_{s-1})$ list each block $i$ exactly $\alpha_i$ times.
--
--   For a coefficient array $c$, put
--   $$
--   P_j(c)=\sum_{t=0}^{n_{i_j}}c_{j,(i_j,t)}X_{i_j,t},\qquad
--   J(c)=I(W)+(P_0(c),\ldots,P_{s-1}(c)),
--   $$
--   and let $Z(c)$ be their common zero set on $W$. Write $A=K[X_{i,t}]$. Choose initial coefficients $c^0$ and a finite set $S\subseteq Z(c^0)$.
--
--   Assume that for every $x\in S$ there are pivot indices $b_i\in\{0,\ldots,n_i\}$, a coordinate tuple $v$ representing $x$ with $v_{i,b_i}=1$, and a polynomial $H\in A$ such that
--   $$
--   H(v)\ne0,\qquad
--   A[H^{-1}]/\bigl(J(c^0)+(X_{i,b_i}-1)_i\bigr)A[H^{-1}]
--   \quad\text{is finite-dimensional over }K.
--   $$
--   Thus the normalized equation scheme is finite on a principal open neighborhood containing the selected point. These algebras may contain nilpotents or additional points. The pivots, representative, and polynomial may depend on $x$; no common neighborhood is assumed.
--
--   Let $C=K[T_{j,w}]$ be the polynomial ring on all coefficient entries, and let $\mathfrak n_c$ be its evaluation maximal ideal at $c$. There exists a Zariski-open subset $U\subseteq\operatorname{Spec}C$ such that
--   $$
--   \mathfrak n_{c^0}\in U,\qquad
--   \mathfrak n_c\in U\ \Longrightarrow\ \text{there exists an injection }S\hookrightarrow Z(c).
--   $$
--   The injection may select different points in each fiber. Positive-dimensional components elsewhere in the initial fiber, nonreduced intersections, empty $S$, and an empty list of equations are allowed.
--
--   **Formalization Note.** This auxiliary incidence-family statement is not a verbatim numbered source theorem. A checked reduction now presents each principal-open equation algebra as an ordinary polynomial quotient with one extra equation $Ht-1=0$. The algebra isomorphism preserves the original mixed and normalization equations, including nilpotents, and transfers finite-dimensionality to this polynomial quotient. At the selected point, the extra coordinate is $H(v)^{-1}$. The implementation also verifies coefficient specialization and the point-evaluation criterion. The sole remaining child is [persistence from finite polynomial slices](p2m:theorem/61b420da-3068-4f26-b812-8bf0a9c76edf). Construction of the universal incidence family, its dimension and dominance, and persistence over an open coefficient neighborhood remain Open. The original formal statement is unchanged.
-- source:
--   P. Philippon, Lemmes de zeros dans les groupes algebriques commutatifs, Bull. SMF 114 (1986), Lemma 3.1 and the mixed-section paragraph, pp. 363–364, https://numdam.org/articles/10.24033/bsmf.2060/ . Stacks Project, Lemma 37.41.5 (Tag 02LO), https://stacks.math.columbia.edu/tag/02LO ; Lemma 37.74.2 (Tag 0F32), https://stacks.math.columbia.edu/tag/0F32 . Auxiliary synthesis of isolated-fiber persistence for the mixed incidence family, with finite equation algebras on explicitly specified principal neighborhoods as hypothesis; not a verbatim source statement. The parent reduction uses finite presentation over a Noetherian ring (Stacks Project Lemma 10.31.4, Tag 00FP, https://stacks.math.columbia.edu/tag/00FP) and the localization-spreading mechanism of Lemma 10.79.2 (Tag 05GF, https://stacks.math.columbia.edu/tag/05GF). The exact algebraic input is Mathlib at revision 0df444a360eaa60ab8c11dca51a86af692955474, Mathlib/Algebra/Module/FinitePresentation.lean, IsLocalizedModule.exists_isLocalizedModule_powers_of_finitePresentation, together with the quotient-localization instance in Mathlib/RingTheory/Localization/Ideal.lean and IsLocalizedModule.linearEquiv. The incidence-family geometry remains an explicit Open obligation.

import Mathlib
import Definitions.Def_PhilipponMultiplicity_GeometricSupport
import Definitions.Def_PhilipponMultiplicity_MixedFlagParameters
set_option autoImplicit false
open scoped BigOperators Topology

namespace PhilipponMultiplicity
open SectionThree SectionThreeSupport

theorem exists_open_preserving_finite_affine_mixed_neighborhoods
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
      (∀ x ∈ S,
        ∃ b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1),
        ∃ v : M.Variable → K, (∀ i, v ⟨i,b i⟩ = 1) ∧
          (∀ i : M.FactorIndex, ∃ h : (fun j => v ⟨i,j⟩) ≠ 0,
            Projectivization.mk K (fun j => v ⟨i,j⟩) h = x i) ∧
          ∃ H : M.CoordinateRing, MvPolynomial.eval v H ≠ 0 ∧
            Module.Finite K ((Localization.Away H) ⧸
              ((MixedFlag.ideal M (M.vanishingIdeal W) l c₀ l.length) ⊔
                Ideal.span (Set.range (fun i : M.FactorIndex =>
                  (MvPolynomial.X (⟨i,b i⟩ : M.Variable) : M.CoordinateRing) - 1))).map
                  (algebraMap M.CoordinateRing (Localization.Away H)))) →
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
