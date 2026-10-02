-- Prove2me | Theorems.Thm_PhilipponMultiplicity_exists_mixed_cut_flag_with_completed_local_conditions
-- name    : PhilipponMultiplicity.exists_mixed_cut_flag_with_completed_local_conditions
-- status  : Open
-- author  : @tomasz
-- created : 2026-10-02T10:13:04.328125+00:00
-- url     : https://prove2.me/theorems/2a7402c2-8ec5-4373-b8a0-be546465fac7
-- title:
--   Mixed cut flags with injective cuts and reduced final quotients after completion
-- statement:
--   Let $W$ be a nonempty irreducible closed subset of $M=\prod_i\mathbf P^{n_i}$ over a Philippon base field $K$. Let $\alpha=(\alpha_i)$ satisfy $0\leq\alpha_i\leq n_i$ and $\sum_i\alpha_i=\dim W$. If $B\subseteq W$ is closed and $W\setminus B$ is nonempty, there is a product linear section $L$ of block codimensions $\alpha_i$ whose intersection with $W$ is finite and disjoint from $B$.
--
--   The section can be defined by an ordered list of block-linear forms $P_0,\ldots,P_{s-1}$, with exactly $\alpha_i$ forms from block $i$. Write $A$ for the multicone polynomial coordinate ring and put $J_0=I(W)$ and $J_{k+1}=J_k+(P_k)$. These equations define exactly the indicated section on multiprojective points.
--
--   For a coordinate tuple $v$ with every block nonzero, put $R_v=A_{\mathfrak m_v}$, where $\mathfrak m_v$ is its evaluation maximal ideal, and let $\widehat R_v$ be its maximal-ideal-adic completion. Writing $V(J)$ for the affine zero set of $J$, the local conclusions are
--   $$
--   v\in V(J_k)\ \Longrightarrow
--   \bigl(\cdot P_k:\widehat R_v/J_k\widehat R_v\longrightarrow
--   \widehat R_v/J_k\widehat R_v\bigr)\text{ is injective},\qquad k<s,
--   $$
--   and
--   $$
--   v\in V(J_s)\ \Longrightarrow\ J_s\widehat R_v\text{ is radical}.
--   $$
--   These completed local conditions supply the geometric input for recovering the ordinary point-local conditions by faithful flatness.
--
--   **Formalization Note.** This is an auxiliary geometric construction, not a verbatim numbered source theorem. The completion is that of the ambient local multicone ring, and the cut ideal is then extended along the composite coordinate-ring map. Empty sections are permitted. The simultaneous selection of the flag and comparison with these completed local rings remain Open.
-- source:
--   Philippon, Lemmes de zeros dans les groupes algebriques commutatifs, Bulletin de la SMF 114 (1986), Lemma 3.1 and the mixed-section paragraph, pp.363–364, https://numdam.org/articles/10.24033/bsmf.2060/ . Nguyen Tien Manh and Duong Quoc Viet, Filter-regular sequences and mixed multiplicities, arXiv:0901.3825v1, Definition 2.1 p.3, notes (i)–(ii) p.4, Proposition 2.6 p.6, https://arxiv.org/abs/0901.3825 . S. L. Kleiman, The transversality of a general translate, Compositio Mathematica 28 (1974), Theorem 2 p.290 and Corollary 4 p.291, https://numdam.org/item/CM_1974__28_3_287_0/ . Stacks Project, Lemma 10.97.3 (tag 00MC), https://stacks.math.columbia.edu/tag/00MC . Auxiliary synthesis: generic filter-regular flags and transversality on the smooth open are the intended geometric inputs. The completed local construction remains Open. Faithful flatness supplies the separate checked descent to the original point-local conditions; radicality ascent for arbitrary Noetherian rings is not asserted.

import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Localization.Ideal
import Definitions.Def_PhilipponMultiplicity_GeometricSupport
set_option autoImplicit false
open scoped BigOperators Topology

namespace PhilipponMultiplicity
open SectionThree SectionThreeSupport

theorem exists_mixed_cut_flag_with_completed_local_conditions
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
              let C := AdicCompletion (IsLocalRing.maximalIdeal R) R
              let f := (algebraMap R C).comp (algebraMap M.CoordinateRing R)
              ∀ Q : C, f (P k) * Q ∈ (J k).map f → Q ∈ (J k).map f) ∧
          (∀ x : M.Point, x ∈ linearSlice M W L ↔
            x ∈ W ∧ ∀ k < l.length, M.eval (P k) x = 0) ∧
          (∀ v : M.Variable → K,
            (∀ i : M.FactorIndex,
              (fun j : Fin (M.ambientDimension i + 1) => v ⟨i,j⟩) ≠ 0) →
            (∀ Q ∈ J l.length, MvPolynomial.eval v Q = 0) →
            let R := Localization.AtPrime (MvPolynomial.vanishingIdeal K {v})
            let C := AdicCompletion (IsLocalRing.maximalIdeal R) R
            let f := (algebraMap R C).comp (algebraMap M.CoordinateRing R)
            ((J l.length).map f).IsRadical) := by sorry

end PhilipponMultiplicity
