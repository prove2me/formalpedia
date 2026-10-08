-- Prove2me | Theorems.Thm_PhilipponMultiplicity_exists_open_preserving_finite_polynomial_mixed_slices
-- name    : PhilipponMultiplicity.exists_open_preserving_finite_polynomial_mixed_slices
-- status  : Open
-- author  : @tomasz
-- created : 2026-10-07T14:49:22.139977+00:00
-- url     : https://prove2.me/theorems/61b420da-3068-4f26-b812-8bf0a9c76edf
-- title:
--   Persistence of mixed sections from finite polynomial slices
-- statement:
--   Let $K$ be a Philippon base field, $M=\prod_i\mathbf P^{n_i}$, and $W\subseteq M$ a closed irreducible subset. Choose integers $0\le\alpha_i\le n_i$ with $\sum_i\alpha_i=\dim W$. Here dimension is the total degree of the actual multigraded quotient Hilbert polynomial. Let $l=(i_0,\ldots,i_{s-1})$ list each block $i$ exactly $\alpha_i$ times, and write $A=K[X_{i,t}]$.
--
--   For a coefficient array $c$, put
--   $$
--   P_j(c)=\sum_{t=0}^{n_{i_j}}c_{j,(i_j,t)}X_{i_j,t},\qquad
--   J(c)=I(W)+(P_0(c),\ldots,P_{s-1}(c)),
--   $$
--   and let $Z(c)$ be the common zero set of these equations on $W$. Choose initial coefficients $c^0$ and a finite set $S\subseteq Z(c^0)$.
--
--   Assume that every $x\in S$ has pivot indices $b_i\in\{0,\ldots,n_i\}$, a representative $v$ with $v_{i,b_i}=1$, a polynomial $H\in A$, and a scalar $a\in K$ such that
--   $$
--   H(v)a=1,\qquad
--   A[t]/\bigl(J(c^0),\ (X_{i,b_i}-1)_i,\ Ht-1\bigr)
--   \quad\text{is finite-dimensional over }K.
--   $$
--   The ideals from $A$ in this display are extended to $A[t]$ through constant polynomials. The variables $X_{i,t}$ are the original affine coordinates; the additional indeterminate $t$ records the inverse of $H$. The quotient retains the actual equations and may contain nilpotents. All choices may depend on $x$, and additional points in this affine equation scheme are allowed.
--
--   Let $C=K[T_{j,w}]$ be the polynomial ring on all coefficient entries, and let $\mathfrak n_c$ denote the evaluation maximal ideal at $c$. There exists a Zariski-open subset $U\subseteq\operatorname{Spec}C$ such that
--   $$
--   \mathfrak n_{c^0}\in U,\qquad
--   \mathfrak n_c\in U\ \Longrightarrow\ \text{there exists an injection }S\hookrightarrow Z(c).
--   $$
--   The injection may choose different points in each fiber. Positive-dimensional components elsewhere in the initial fiber, nonreduced intersections, empty $S$, and an empty equation list are allowed.
--
--   **Formalization Note.** The checked reduction constructs the universal coefficient algebra, proves that its fiber at the initial coefficient point is isomorphic to the finite polynomial quotient in this hypothesis, and proves quasi-finiteness along that fiber. The remaining [quasi-finite mixed-family persistence theorem](https://prove2.me/theorems/21d579ca-f415-4857-ab2e-230dd9e2c4a2) supplies the geometric persistence step. The universal family, its coefficient-fiber identification, and its initial-fiber quasi-finiteness are established in the reduction; dimension/dominance and open-neighborhood persistence remain Open. The argument retains the original equations and their possible nilpotents.
-- source:
--   P. Philippon, Lemmes de zeros dans les groupes algebriques commutatifs, Bull. SMF 114 (1986), Lemma 3.1 and the mixed-section paragraph, pp. 363–364, https://numdam.org/articles/10.24033/bsmf.2060/ . Stacks Project, Lemma 37.41.5 (Tag 02LO), https://stacks.math.columbia.edu/tag/02LO , and Lemma 37.74.2 (Tag 0F32), https://stacks.math.columbia.edu/tag/0F32 , motivate the remaining isolated-fiber persistence argument. This is an auxiliary synthesis with finite polynomial presentations of the normalized initial slices, not a verbatim source theorem. The parent proves the algebraic conversion using the localization universal property and its compatibility with quotients: Stacks Project, Proposition 10.9.3 and Proposition 10.9.14, Section 10.9 (Tag 00CM), https://stacks.math.columbia.edu/tag/00CM . The exact reused formal input is Localization.awayEquivAdjoin in Mathlib/RingTheory/Localization/Away/AdjoinRoot.lean at revision 0df444a360eaa60ab8c11dca51a86af692955474, combined with Ideal.quotientEquivAlg and DoubleQuot.quotQuotEquivQuotSupₐ. The published child leaves the incidence-family geometry Open.

import Mathlib
import Definitions.Def_PhilipponMultiplicity_GeometricSupport
import Definitions.Def_PhilipponMultiplicity_MixedFlagParameters
set_option autoImplicit false
open scoped BigOperators Topology

namespace PhilipponMultiplicity
open SectionThree SectionThreeSupport

theorem exists_open_preserving_finite_polynomial_mixed_slices
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
          ∃ H : M.CoordinateRing, ∃ a : K, MvPolynomial.eval v H * a = 1 ∧
            Module.Finite K ((Polynomial M.CoordinateRing) ⧸
              (((MixedFlag.ideal M (M.vanishingIdeal W) l c₀ l.length) ⊔
                Ideal.span (Set.range (fun i : M.FactorIndex =>
                  (MvPolynomial.X (⟨i,b i⟩ : M.Variable) : M.CoordinateRing) - 1))).map
                  Polynomial.C ⊔ Ideal.span {Polynomial.C H * Polynomial.X - 1}))) →
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
