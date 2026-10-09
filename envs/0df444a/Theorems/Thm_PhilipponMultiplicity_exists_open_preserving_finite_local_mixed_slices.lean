-- Prove2me | Theorems.Thm_PhilipponMultiplicity_exists_open_preserving_finite_local_mixed_slices
-- name    : PhilipponMultiplicity.exists_open_preserving_finite_local_mixed_slices
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-07T13:00:56.314027+00:00
-- url     : https://prove2.me/theorems/15ace125-00ef-4ed1-8f91-53698fcbcc31
-- title:
--   Persistence of mixed sections from finite normalized local algebras
-- statement:
--   Let $K$ be a Philippon base field, $M=\prod_i\mathbf P^{n_i}$, and $W\subseteq M$ a closed irreducible subset. Choose integers $0\le\alpha_i\le n_i$ with $\sum_i\alpha_i=\dim W$. Dimension here is the total degree of the actual multigraded quotient Hilbert polynomial. Let $l=(i_0,\ldots,i_{s-1})$ list each block $i$ exactly $\alpha_i$ times.
--
--   For a coefficient array $c$, set
--   $$
--   P_j(c)=\sum_{t=0}^{n_{i_j}}c_{j,(i_j,t)}X_{i_j,t},\qquad
--   J(c)=I(W)+(P_0(c),\ldots,P_{s-1}(c)),
--   $$
--   and let $Z(c)$ be their common zero set on $W$. Write $A=K[X_{i,t}]$. Choose initial coefficients $c^0$ and a finite set $S\subseteq Z(c^0)$.
--
--   Assume that for every $x\in S$ there are pivot indices $b_i\in\{0,\ldots,n_i\}$ and a coordinate tuple $v$ representing $x$ with $v_{i,b_i}=1$ such that the normalized local equation algebra
--   $$
--   B_{x,b,v}=A_{\mathfrak m_v}/\bigl(J(c^0)+(X_{i,b_i}-1)_i\bigr)A_{\mathfrak m_v},
--   \qquad \mathfrak m_v=\ker(\operatorname{ev}_v:A\to K),
--   $$
--   is finite-dimensional over $K$. These algebras may contain nilpotents. The pivots and representatives may depend on $x$.
--
--   Let $C=K[T_{j,w}]$ be the polynomial ring on all coefficient entries, and let $\mathfrak n_c$ be its evaluation maximal ideal at $c$. There exists a Zariski-open subset $U\subseteq\operatorname{Spec}C$ such that
--   $$
--   \mathfrak n_{c^0}\in U,\qquad
--   \mathfrak n_c\in U\ \Longrightarrow\ \text{there exists an injection }S\hookrightarrow Z(c).
--   $$
--   This supplies persistence in number of the prescribed isolated mixed intersections under changes of coefficients. The injection may select different points in each fiber. Positive-dimensional components elsewhere in the initial fiber, nonreduced local intersections, empty $S$, and an empty list of equations are allowed.
--
--   **Formalization Note.** This auxiliary incidence-family statement is not a verbatim numbered source theorem. A checked algebraic reduction now replaces each finite point-local quotient by a finite quotient on a principal open neighborhood containing the point. Over the Noetherian polynomial ring, finiteness of the local quotient implies finite presentation as a module. Localization can then be achieved by inverting one polynomial $H$ with $H(v)\ne0$; uniqueness of localized modules transfers finiteness to the quotient on this principal open. The actual mixed equations and nilpotents are retained. The sole remaining child is [persistence from finite principal neighborhoods](p2m:theorem/2eac4ece-8a33-49bc-afda-520b38f3f704). Construction and comparison of the mixed incidence scheme, dimension and dominance, and the open-neighborhood persistence argument remain Open. The original formal statement is unchanged.
-- source:
--   P. Philippon, Lemmes de zeros dans les groupes algebriques commutatifs, Bull. SMF 114 (1986), Lemma 3.1 and the mixed-section paragraph, pp. 363–364, https://numdam.org/articles/10.24033/bsmf.2060/ . Stacks Project, Lemma 37.41.5 (Tag 02LO), https://stacks.math.columbia.edu/tag/02LO ; Lemma 37.74.2 (Tag 0F32), https://stacks.math.columbia.edu/tag/0F32 ; Lemma 29.29.4 (Tag 02FZ), https://stacks.math.columbia.edu/tag/02FZ . Auxiliary synthesis of isolated-fiber persistence for the mixed incidence family, with finite-dimensional normalized local coordinate algebras as the concrete hypothesis. It is not claimed to be a verbatim source statement. The parent proves finiteness using the point-cone equations, pivot normalization, and finiteness across a finitely generated nilpotent kernel; compare Stacks Project Lemma 10.52.8 (Tag 00J0), https://stacks.math.columbia.edu/tag/00J0 , and Lemma 10.60.5 (Tag 00KH), https://stacks.math.columbia.edu/tag/00KH . The incidence-scheme construction, comparison, dimension, dominance, and openness remain explicit Open obligations.

import Mathlib
import Definitions.Def_PhilipponMultiplicity_GeometricSupport
import Definitions.Def_PhilipponMultiplicity_MixedFlagParameters
set_option autoImplicit false
open scoped BigOperators Topology

namespace PhilipponMultiplicity
open SectionThree SectionThreeSupport

theorem exists_open_preserving_finite_local_mixed_slices
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
          Module.Finite K ((Localization.AtPrime (MvPolynomial.vanishingIdeal K {v})) ⧸
            ((MixedFlag.ideal M (M.vanishingIdeal W) l c₀ l.length) ⊔
              Ideal.span (Set.range (fun i : M.FactorIndex =>
                (MvPolynomial.X (⟨i,b i⟩ : M.Variable) : M.CoordinateRing) - 1))).map
                (algebraMap M.CoordinateRing
                  (Localization.AtPrime (MvPolynomial.vanishingIdeal K {v}))))) →
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
