-- Prove2me | Theorems.Thm_PhilipponMultiplicity_exists_principal_open_regular_point_mixed_zero_locus
-- name    : PhilipponMultiplicity.exists_principal_open_regular_point_mixed_zero_locus
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-06T01:37:08.877328+00:00
-- url     : https://prove2.me/theorems/648687d4-3710-4e11-b973-e9ec865463a2
-- title:
--   A principal open family of mixed sections with regular point-local quotients
-- statement:
--   Let $K$ be a Philippon base field and $M=\prod_i\mathbf P^{n_i}$ the given finite multiprojective space. Let $W\subseteq M$ be closed and irreducible. Choose integers $0\le\alpha_i\le n_i$ with $\sum_i\alpha_i=\dim W$, and a closed subset $B\subseteq W$ with $W\setminus B\ne\varnothing$.
--
--   Fix an ordered list $l=(i_0,\ldots,i_{s-1})$ containing each block $i$ exactly $\alpha_i$ times. For a coefficient tuple $c$, put
--   $$
--   P_j(c)=\sum_{t=0}^{n_{i_j}}c_{j,(i_j,t)}X_{i_j,t},\qquad
--   J_s(c)=I(W)+(P_0(c),\ldots,P_{s-1}(c))\subseteq A=K[X_{i,t}],
--   $$
--   and let $Z(c)$ be the common zero set of these equations on $W$.
--
--   There exists a nonzero polynomial $F$ in the coefficient entries such that, whenever $F(c)\ne0$, the set $Z(c)$ is finite and disjoint from $B$. Moreover, if $v$ is any coordinate tuple with every block nonzero and $P(v)=0$ for every $P\in J_s(c)$, then, with $\mathfrak m_v=\{P\in A:P(v)=0\}$,
--   $$
--   A_{\mathfrak m_v}/J_s(c)A_{\mathfrak m_v}
--   \quad\text{is a regular local ring}.
--   $$
--   This describes the local regularity of a general mixed section on the punctured multicone, including its affine scaling directions.
--
--   **Formalization Note.** This is an auxiliary coefficient-space formulation of generic proper and transverse mixed intersection, not a verbatim source theorem. Regularity concerns the actual localized quotient by the mixed ideal, not merely its reduced zero set. Rows of $c$ have coordinates in every block, although each equation uses only its selected block. Empty sections and zero-length lists are allowed. The statement does not require choosing equations, Jacobian minors, or local presentations.
--
--   **Current reduction.** For every multihomogeneous ideal with finite projective zero set, radicality at a nonzero-block point representative implies regularity of the actual localized quotient. The proof uses the projective Nullstellensatz, homogeneous separation of the finite points, and explicit linear equations for a single point cone with an identity Jacobian minor. The remaining Open input is [a principal open mixed-section family with radical point-local ideals](https://prove2.me/theorems/c926e10d-9300-4586-a988-3e3cb97677b0); it supplies generic finiteness, boundary avoidance, and local radicality. The original coefficient polynomial and formal target statement are retained.
-- source:
--   Philippon, Lemmes de zeros dans les groupes algebriques commutatifs, Bull. SMF 114 (1986), pp.363–364, Lemma 3.1 and the mixed-section paragraph, https://numdam.org/articles/10.24033/bsmf.2060/ . S. L. Kleiman, The transversality of a general translate, Compositio Mathematica 28 (1974), Theorem 2(i),(ii), p.290, and Corollary 4(i),(ii), p.291, https://numdam.org/item/CM_1974__28_3_287_0.pdf . Auxiliary synthesis: generic proper/transverse mixed intersection, avoidance of the boundary and singular locus, passage to a principal open in the actual coefficient space, and regularity of the actual point-local multicone quotient remain Open. The parent reduction proves the passage from regular local quotients to explicit localized ideal generators and nonvanishing coordinate Jacobian minors, reusing the proved regular-local conormal identity from Stacks Project, Lemma 10.106.4, Tag 00NR, https://stacks.math.columbia.edu/tag/00NR .

import Mathlib
import Definitions.Def_PhilipponMultiplicity_GeometricSupport
import Definitions.Def_PhilipponMultiplicity_MixedFlagParameters
set_option autoImplicit false
open scoped BigOperators Topology

namespace PhilipponMultiplicity
open SectionThree SectionThreeSupport

theorem exists_principal_open_regular_point_mixed_zero_locus
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
                IsRegularLocalRing
                  ((Localization.AtPrime (MvPolynomial.vanishingIdeal K {v})) ⧸
                    (MixedFlag.ideal M (M.vanishingIdeal W) l c l.length).map
                      (algebraMap M.CoordinateRing
                        (Localization.AtPrime (MvPolynomial.vanishingIdeal K {v}))))) := by sorry

end PhilipponMultiplicity
