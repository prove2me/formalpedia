-- Prove2me | Theorems.Thm_PhilipponMultiplicity_exists_associated_prime_avoiding_smooth_mixed_cut_flag
-- name    : PhilipponMultiplicity.exists_associated_prime_avoiding_smooth_mixed_cut_flag
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-04T18:08:05.508698+00:00
-- url     : https://prove2.me/theorems/d9adee76-69d2-422b-85da-e1b8e22720f9
-- title:
--   Mixed cut flags avoiding associated primes with smooth final multicone
-- statement:
--   Let $K$ be a Philippon base field and $M=\prod_i\mathbf P^{n_i}$ a finite product of projective spaces. Let $W\subseteq M$ be a nonempty irreducible closed subset, and let $0\leq\alpha_i\leq n_i$ satisfy $\sum_i\alpha_i=\dim W$. If $B\subseteq W$ is closed and $W\setminus B\ne\varnothing$, there are vector subspaces $L_i\subseteq K^{n_i+1}$ of codimension $\alpha_i$ whose mixed section of $W$ is finite and disjoint from $B$.
--
--   The section admits an ordered list of block-linear equations $P_0,\ldots,P_{s-1}$, with exactly $\alpha_i$ equations from block $i$. In the multicone polynomial ring $A$, set $J_0=I(W)$, $J_{k+1}=J_k+(P_k)$, and $Q_k=A/J_k$. These equations cut out the same mixed section on multiprojective points, and they have the following two properties.
--
--   For $0\leq k<s$, the class of $P_k$ avoids every associated prime $\mathfrak q\in\operatorname{Ass}_{Q_k}(Q_k)$ at which no coordinate block vanishes identically:
--   $$
--   \left(\forall i\;\exists j\; \overline X_{ij}\notin\mathfrak q\right)
--   \ \Longrightarrow\ \overline P_k\notin\mathfrak q.
--   $$
--   For every prime $\mathfrak q$ of $Q_s$ with the same nonzero-block property, $Q_s$ is smooth over $K$ at $\mathfrak q$.
--
--   **Formalization Note.** This is the generic geometric selection input: associated-prime avoidance for the successive cuts and smoothness on the punctured final multicone. It contains no point-local ideal-membership implication or regular-local-ring conclusion. The final smoothness assertion concerns all scheme points of the punctured affine cone, including its coordinate-scaling directions. Empty final sections and zero-dimensional $W$ are allowed. The statement is an auxiliary synthesis of filter-regular selection and generic transversality; the simultaneous choice and the comparison with the concrete multicone remain Open.
--
--   **Proof status.** A checked reduction proves that successive associated-prime avoidance can be imposed inside every nonempty principal open of coefficient matrices over an infinite field. Its sole remaining input is [a principal-open family of smooth mixed sections](/theorems/cb087b60-bd87-46f8-8672-81234ffb113d); that input contains no associated-prime avoidance hypothesis. The reduction proves the finite-subspace selection, row specialization, prefix-ideal invariance, block homogeneity, and exact assembly of the flag. The geometric existence and the punctured-multicone comparison remain Open.
-- source:
--   Philippon, Lemmes de zeros dans les groupes algebriques commutatifs, Bull. SMF 114 (1986), Lemma 3.1 and the mixed-section paragraph, pp.363–364, https://numdam.org/articles/10.24033/bsmf.2060/ . Nguyen Tien Manh and Duong Quoc Viet, Filter-regular sequences and mixed multiplicities, arXiv:0901.3825v1, Definition 2.1 p.3, notes (i)–(ii) p.4 and Proposition 2.6 p.6, https://arxiv.org/pdf/0901.3825 . S. L. Kleiman, The transversality of a general translate, Compositio Mathematica 28 (1974), Theorem 2(i),(ii) p.290 and Corollary 4 p.291, https://numdam.org/item/CM_1974__28_3_287_0.pdf . Auxiliary synthesis, not a verbatim source assertion: impose finite associated-prime avoidance off the multigraded irrelevant locus, and choose the final mixed section transverse to the smooth locus, avoiding B and the singular locus. Its punctured multicone is locally a product with a torus. All these geometric choices and the coordinate-ring comparison are required formalization work.

import Mathlib
import Definitions.Def_PhilipponMultiplicity_GeometricSupport
set_option autoImplicit false
open scoped BigOperators Topology

namespace PhilipponMultiplicity
open SectionThree SectionThreeSupport

theorem exists_associated_prime_avoiding_smooth_mixed_cut_flag
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K) :
    ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ B : Set M.Point, @IsClosed _ M.zariskiTopology B → B ⊆ W →
      (W \ B).Nonempty →
      ∃ L : ∀ i : M.FactorIndex, Submodule K (Fin (M.ambientDimension i + 1) → K),
        (∀ i, Module.finrank K (L i) + α i = M.ambientDimension i + 1) ∧
        (linearSlice M W L).Finite ∧ Disjoint (linearSlice M W L) B ∧
        ∃ (l : List M.FactorIndex) (P : ℕ → M.CoordinateRing)
          (J : ℕ → Ideal M.CoordinateRing),
          (∀ i, l.count i = α i) ∧ J 0 = M.vanishingIdeal W ∧
          (∀ k (hk : k < l.length),
            M.IsHomogeneous (P k) (Pi.single l[k] 1) ∧
            J (k+1) = J k ⊔ Ideal.span {P k} ∧
            ∀ q ∈ associatedPrimes
                (M.CoordinateRing ⧸ J k) (M.CoordinateRing ⧸ J k),
              (∀ i : M.FactorIndex, ∃ j : Fin (M.ambientDimension i + 1),
                Ideal.Quotient.mk (J k) (MvPolynomial.X ⟨i,j⟩) ∉ q) →
              Ideal.Quotient.mk (J k) (P k) ∉ q) ∧
          (∀ x : M.Point, x ∈ linearSlice M W L ↔
            x ∈ W ∧ ∀ k < l.length, M.eval (P k) x = 0) ∧
          (∀ q : PrimeSpectrum (M.CoordinateRing ⧸ J l.length),
            (∀ i : M.FactorIndex, ∃ j : Fin (M.ambientDimension i + 1),
              Ideal.Quotient.mk (J l.length) (MvPolynomial.X ⟨i,j⟩) ∉ q.asIdeal) →
            Algebra.IsSmoothAt K q.asIdeal) := by sorry

end PhilipponMultiplicity
