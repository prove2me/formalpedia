-- Prove2me | Theorems.Thm_PhilipponMultiplicity_exists_mixed_cut_flag_with_regular_local_final_quotients
-- name    : PhilipponMultiplicity.exists_mixed_cut_flag_with_regular_local_final_quotients
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-04T16:20:34.876984+00:00
-- url     : https://prove2.me/theorems/2e1804de-ff01-4104-a3e5-216cabbd0bb3
-- title:
--   Mixed cut flags with regular final local quotients
-- statement:
--   Let $K$ be a Philippon base field and let $M=\prod_i\mathbf P^{n_i}$ be a finite product of projective spaces. Let $W\subseteq M$ be a nonempty irreducible closed subset. Suppose $0\leq\alpha_i\leq n_i$ and $\sum_i\alpha_i=\dim W$. For every closed subset $B\subseteq W$ with $W\setminus B\ne\varnothing$, there are vector subspaces $L_i\subseteq K^{n_i+1}$ of codimension $\alpha_i$ such that $W\cap\prod_i\mathbf P(L_i)$ is finite and disjoint from $B$.
--
--   These subspaces admit an ordered list of block-linear equations $P_0,\ldots,P_{s-1}$, with exactly $\alpha_i$ equations from block $i$, defining this same section on multiprojective points. In the multicone coordinate ring $A$, put $J_0=I(W)$ and $J_{k+1}=J_k+(P_k)$. For a coordinate tuple $v$ with every block nonzero, let $\mathfrak m_v$ be its evaluation maximal ideal and set $R_v=A_{\mathfrak m_v}$. The flag satisfies
--   $$
--   v\in V(J_k)\ \Longrightarrow\
--   \bigl(\cdot P_k:R_v/J_kR_v\longrightarrow R_v/J_kR_v\bigr)
--   \text{ is injective}\qquad(0\leq k<s),
--   $$
--   and
--   $$
--   v\in V(J_s)\ \Longrightarrow\ R_v/J_sR_v
--   \text{ is a regular local ring}.
--   $$
--
--   This strengthens the final reducedness condition to regularity and supplies a geometric input for passing to completed local rings. Empty final sections are permitted, and no regularity is required of intermediate quotients.
--
--   **Formalization Note.** A checked reduction proves these local conditions from [associated-prime avoidance and smoothness of the final punctured multicone](https://prove2.me/theorems/d9adee76-69d2-422b-85da-e1b8e22720f9). The proof establishes localized multiplication injectivity, the nonzero-coordinate condition for primes below an evaluation ideal, and regularity of the final localized quotient via smoothness and the quotient-localization equivalence. The generic geometric choice remains Open. All original hypotheses, witnesses, and the formal statement are unchanged; no regularity is required of intermediate quotients.
-- source:
--   Philippon, Lemmes de zeros dans les groupes algebriques commutatifs, Bulletin de la SMF 114 (1986), Lemma 3.1 and the mixed-section paragraph, pp.363–364, https://numdam.org/articles/10.24033/bsmf.2060/ . Nguyen Tien Manh and Duong Quoc Viet, Filter-regular sequences and mixed multiplicities, arXiv:0901.3825v1, Definition 2.1 p.3, notes (i)–(ii) p.4, Proposition 2.6 p.6, https://arxiv.org/pdf/0901.3825 . S. L. Kleiman, The transversality of a general translate, Compositio Mathematica 28 (1974), Theorem 2(i),(ii) p.290 and Corollary 4 p.291, https://numdam.org/item/CM_1974__28_3_287_0.pdf . Auxiliary synthesis, not a verbatim source assertion: choose a generic flag avoiding associated primes off the multigraded irrelevant locus, with final section transverse to the smooth locus and disjoint from B and the singular locus. On nonzero coordinate blocks the multicone projection is locally a product with a torus; its local quotient over the smooth zero-dimensional section is regular. The simultaneous choice and scheme-to-coordinate-ring comparison are the Open geometric obligation.

import Mathlib
import Definitions.Def_PhilipponMultiplicity_GeometricSupport
set_option autoImplicit false
open scoped BigOperators Topology

namespace PhilipponMultiplicity
open SectionThree SectionThreeSupport

theorem exists_mixed_cut_flag_with_regular_local_final_quotients
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
            ∀ v : M.Variable → K,
              (∀ i : M.FactorIndex,
                (fun j : Fin (M.ambientDimension i + 1) => v ⟨i,j⟩) ≠ 0) →
              (∀ Q ∈ J k, MvPolynomial.eval v Q = 0) →
              let R := Localization.AtPrime (MvPolynomial.vanishingIdeal K {v})
              let f := algebraMap M.CoordinateRing R
              ∀ Q : R, f (P k) * Q ∈ (J k).map f → Q ∈ (J k).map f) ∧
          (∀ x : M.Point, x ∈ linearSlice M W L ↔
            x ∈ W ∧ ∀ k < l.length, M.eval (P k) x = 0) ∧
          (∀ v : M.Variable → K,
            (∀ i : M.FactorIndex,
              (fun j : Fin (M.ambientDimension i + 1) => v ⟨i,j⟩) ≠ 0) →
            (∀ Q ∈ J l.length, MvPolynomial.eval v Q = 0) →
            let R := Localization.AtPrime (MvPolynomial.vanishingIdeal K {v})
            IsRegularLocalRing (R ⧸ (J l.length).map (algebraMap M.CoordinateRing R))) := by sorry

end PhilipponMultiplicity
