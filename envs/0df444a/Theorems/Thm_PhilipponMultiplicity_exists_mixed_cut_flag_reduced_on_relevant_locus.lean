-- Prove2me | Theorems.Thm_PhilipponMultiplicity_exists_mixed_cut_flag_reduced_on_relevant_locus
-- name    : PhilipponMultiplicity.exists_mixed_cut_flag_reduced_on_relevant_locus
-- status  : Open
-- author  : @tomasz
-- created : 2026-10-01T16:39:54.1433+00:00
-- url     : https://prove2.me/theorems/b6f41518-ee71-44f1-ab50-6b0f11374892
-- title:
--   Mixed cut flags reduced on the relevant locus
-- statement:
--   Let $K$ be a Philippon base field, $M=\prod_i\mathbf P^{N_i}$, and $W\subseteq M$ a closed irreducible subvariety. Let $B\subsetneq W$ be closed, and fix $0\le\alpha_i\le N_i$ with $\sum_i\alpha_i=\dim W$.
--
--   There are linear subspaces $L_i$ of codimension $\alpha_i$ such that $Z=W\cap\prod_i L_i$ is finite and disjoint from $B$, together with an ordered list $i_0,\ldots,i_{n-1}$, block-linear forms $P_k$, and actual cut ideals $J_k$ satisfying
--   $$
--   \#\{k:i_k=i\}=\alpha_i,\qquad J_0=I(W),\qquad
--   \deg P_k=e_{i_k},\qquad J_{k+1}=J_k+(P_k).
--   $$
--   The equations define the chosen section on $W$:
--   $$
--   x\in Z\quad\Longleftrightarrow\quad x\in W\ \text{and}\ P_k(x)=0\text{ for every }k<n.
--   $$
--   At each step, a finite minimal multihomogeneous primary decomposition $J_k=\bigcap_jQ_{kj}$ can be chosen so that $P_k$ avoids every relevant radical $\sqrt{Q_{kj}}$, including those of embedded components. Relevance means that the multiprojective irrelevant ideal $\mathfrak b$ is not contained in that prime.
--
--   The final cut is reduced on the relevant locus: for every prime $\mathfrak p$ with $\mathfrak b\not\subseteq\mathfrak p$, the ideal $J_nR_{\mathfrak p}$ is radical. Equivalently, its quotient has no nonzero nilpotents. The prime need not be homogeneous. Irrelevant primary components of $J_n$ are allowed.
--
--   **Formalization Note.** This is an auxiliary geometric selection statement combining generic primary-prime avoidance with a reduced general mixed section. It is not a verbatim numbered theorem from one source. The simultaneous generic choice and its translation to actual localized homogeneous-coordinate ideals remain Open. No equality with $I(Z)$, Hilbert-function comparison, or numerical intersection count is assumed. Empty sections, empty cut lists, and zero-dimensional varieties are included.
--
--
--   **Verified coordinate-local reduction.** The accepted sketch proves that finitely many standard principal opens of the multicone cover all relevant primes. Injectivity of each cutting form on each localized quotient implies avoidance of every relevant associated prime. Existing Proved primary-decomposition theorems turn this into the exact primary-prime avoidance condition, including embedded components. Radicality of the final cut on these principal opens implies radicality at every relevant prime, even if that prime is not homogeneous.
--
--   The only Open dependency is [mixed cut flags with coordinate-local conditions](https://prove2.me/theorems/a774d51e-7dc7-439a-8661-2093dab4a755). It asks for the geometric section, explicit equations, injective localized cuts, and a reduced final localized quotient. It does not assume primary-prime avoidance or reducedness at every relevant prime. These implications are proved in the sketch. The generic geometric construction remains Open.
-- source:
--   Philippon, Lemmes de zeros dans les groupes algebriques commutatifs, Bulletin de la SMF 114 (1986), Lemma 3.1 and the following mixed-section paragraph, pp. 363–364, https://numdam.org/articles/10.24033/bsmf.2060/ . Nguyen Tien Manh and Duong Quoc Viet, Filter-regular sequences and mixed multiplicities, arXiv:0901.3825v1, Definition 2.1, p. 3, Proposition 2.4, p. 5, and Proposition 2.6, p. 6, https://arxiv.org/abs/0901.3825 . S. L. Kleiman, The transversality of a general translate, Compositio Mathematica 28 (1974), Theorem 2, p. 290, and Corollary 4, p. 291, https://numdam.org/item/CM_1974__28_3_287_0/ . Auxiliary synthesis: apply transversality on the smooth open subset of W, avoid its proper closed complement together with B, and make the cutting flag generic for relevant associated-prime avoidance. The bridge from scheme reducedness to radical localizations on the relevant multicone is part of this Open assertion.

import Definitions.Def_PhilipponMultiplicity_GeometricSupport
set_option autoImplicit false
open scoped BigOperators Topology

namespace PhilipponMultiplicity
open SectionThree SectionThreeSupport

theorem exists_mixed_cut_flag_reduced_on_relevant_locus
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
            ∃ A : PrimaryDecomposition M (J k), ∀ j : Fin A.count,
              Hilbert.IsRelevant K M.factorCount M.ambientDimension (A.component j).radical →
              P k ∉ (A.component j).radical) ∧
          (∀ x : M.Point, x ∈ linearSlice M W L ↔
            x ∈ W ∧ ∀ k < l.length, M.eval (P k) x = 0) ∧
          (∀ q : PrimeSpectrum M.CoordinateRing,
            Hilbert.IsRelevant K M.factorCount M.ambientDimension q.asIdeal →
            ((J l.length).map
              (algebraMap M.CoordinateRing (Localization.AtPrime q.asIdeal))).IsRadical) := by sorry

end PhilipponMultiplicity
