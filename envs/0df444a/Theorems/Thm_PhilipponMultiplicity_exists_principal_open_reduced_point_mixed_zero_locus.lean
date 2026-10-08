-- Prove2me | Theorems.Thm_PhilipponMultiplicity_exists_principal_open_reduced_point_mixed_zero_locus
-- name    : PhilipponMultiplicity.exists_principal_open_reduced_point_mixed_zero_locus
-- status  : Open
-- author  : @tomasz
-- created : 2026-10-07T09:13:27.18899+00:00
-- url     : https://prove2.me/theorems/c926e10d-9300-4586-a988-3e3cb97677b0
-- title:
--   A principal open family of mixed sections with radical point-local ideals
-- statement:
--   Let $K$ be a Philippon base field, let $M=\prod_i\mathbf P^{n_i}$, and let $W\subseteq M$ be closed and irreducible. Choose integers $0\le\alpha_i\le n_i$ with $\sum_i\alpha_i=\dim W$, where dimension is the total degree of the actual quotient Hilbert polynomial. Let $B\subseteq W$ be closed with $W\setminus B\ne\varnothing$.
--
--   Fix an ordered list $l=(i_0,\ldots,i_{s-1})$ containing each block $i$ exactly $\alpha_i$ times. For coefficient arrays $c$, define
--   $$
--   P_j(c)=\sum_{t=0}^{n_{i_j}}c_{j,(i_j,t)}X_{i_j,t},\qquad
--   J_s(c)=I(W)+(P_0(c),\ldots,P_{s-1}(c))\subseteq A=K[X_{i,t}],
--   $$
--   and let $Z(c)\subseteq W$ be the common zero set of the $P_j(c)$.
--
--   There is a nonzero polynomial $F$ in the coefficient entries such that $F(c)\ne0$ implies that $Z(c)$ is finite and disjoint from $B$. Furthermore, for every coordinate tuple $v$ with each block nonzero and every element of $J_s(c)$ vanishing at $v$, the localized ideal is radical:
--   $$
--   J_s(c)A_{\mathfrak m_v}\text{ is radical},\qquad
--   \mathfrak m_v=\{Q\in A:Q(v)=0\}.
--   $$
--   Thus the actual mixed-section scheme is reduced at all of its nonzero-block point representatives. The statement retains the affine scaling directions and permits empty sections and zero-length lists.
--
--   **Formalization Note.** This is an auxiliary coefficient-space formulation of generic proper and reduced mixed intersection, not a verbatim source theorem. The ideal is the actual sum of the vanishing ideal and cutting equations. Radicality of its localization is an assertion about this ideal, not merely its set of zeros. Rows contain coefficients in every block, although each equation uses only its selected block. Generic finiteness, boundary avoidance, passage to a principal open coefficient condition, and comparison with the concrete multiprojective point model remain Open. The parent reduction proves that finiteness and this local radicality imply regularity of the required point-local quotients.
-- source:
--   P. Philippon, Lemmes de zeros dans les groupes algebriques commutatifs, Bull. SMF 114 (1986), pp.363–364, Lemma 3.1 and the mixed-section paragraph, https://numdam.org/articles/10.24033/bsmf.2060/ . S. L. Kleiman, The transversality of a general translate, Compositio Mathematica 28 (1974), Theorem 2(i),(ii), p.290, Corollary 4(i),(ii), p.291, and Remark 7 (the reduced variant), p.292, https://numdam.org/item/CM_1974__28_3_287_0.pdf . Auxiliary synthesis: generic proper mixed intersection and boundary avoidance, generic reducedness, and transfer to the actual coefficient and multicone ideals remain Open. The parent proves the local regularity consequence by projective Nullstellensatz, separation of finitely many points, and explicit linear equations for a point cone with an identity Jacobian minor.

import Mathlib
import Definitions.Def_PhilipponMultiplicity_GeometricSupport
import Definitions.Def_PhilipponMultiplicity_MixedFlagParameters
set_option autoImplicit false
open scoped BigOperators Topology

namespace PhilipponMultiplicity
open SectionThree SectionThreeSupport

theorem exists_principal_open_reduced_point_mixed_zero_locus
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K) :
    ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ B : Set M.Point, @IsClosed _ M.zariskiTopology B → B ⊆ W →
      (W \ B).Nonempty →
      ∀ l : List M.FactorIndex, (∀ i, l.count i = α i) →
        ∃ F : MvPolynomial (Fin l.length × M.Variable) K, F ≠ 0 ∧
          ∀ c : Fin l.length → M.Variable → K,
            MvPolynomial.eval (Function.uncurry c) F ≠ 0 →
            ({x : M.Point | x ∈ W ∧
              ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c j) x = 0}).Finite ∧
            Disjoint {x : M.Point | x ∈ W ∧
              ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c j) x = 0} B ∧
            (∀ v : M.Variable → K,
                (∀ i : M.FactorIndex,
                  (fun j : Fin (M.ambientDimension i + 1) => v ⟨i,j⟩) ≠ 0) →
                (∀ P ∈ MixedFlag.ideal M (M.vanishingIdeal W) l c l.length,
                  MvPolynomial.eval v P = 0) →
                ((MixedFlag.ideal M (M.vanishingIdeal W) l c l.length).map
                  (algebraMap M.CoordinateRing
                    (Localization.AtPrime (MvPolynomial.vanishingIdeal K {v})))).IsRadical) := by sorry

end PhilipponMultiplicity
