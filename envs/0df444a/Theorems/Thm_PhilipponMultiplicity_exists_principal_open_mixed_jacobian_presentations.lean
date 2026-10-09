-- Prove2me | Theorems.Thm_PhilipponMultiplicity_exists_principal_open_mixed_jacobian_presentations
-- name    : PhilipponMultiplicity.exists_principal_open_mixed_jacobian_presentations
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-05T21:30:17.98126+00:00
-- url     : https://prove2.me/theorems/f4809fcb-0a9b-4823-b61a-1b63c83afec1
-- title:
--   Generic mixed sections admit local equations with a nonvanishing Jacobian minor
-- statement:
--   Let $K$ be a Philippon base field and $M=\prod_i\mathbf P^{n_i}$ the given finite multiprojective space. Let $W\subseteq M$ be closed and irreducible. Choose $0\le\alpha_i\le n_i$ with $\sum_i\alpha_i=\dim W$, and a closed subset $B\subseteq W$ with $W\setminus B\ne\varnothing$.
--
--   Fix an ordered list $l=(i_0,\ldots,i_{s-1})$ containing each block $i$ exactly $\alpha_i$ times. For coefficients $c$, let
--   $$
--   P_j(c)=\sum_{t=0}^{n_{i_j}}c_{j,(i_j,t)}X_{i_j,t},\qquad
--   J_s(c)=I(W)+(P_0(c),\ldots,P_{s-1}(c))\subseteq A=K[X_{i,t}].
--   $$
--   Let $Z(c)$ be their common zero set on $W$.
--
--   There is a nonzero polynomial $F$ in all coefficient entries such that, whenever $F(c)\ne0$, the set $Z(c)$ is finite and disjoint from $B$, and the following holds. For every coordinate tuple $v$ with each block nonzero and with $P(v)=0$ for all $P\in J_s(c)$, put $\mathfrak m_v=\{P:P(v)=0\}$. There are an integer $r\ge0$, polynomials $Q_1,\ldots,Q_r\in A$, and distinct coordinate variables $e_1,\ldots,e_r$ such that
--   $$
--   Q_j(v)=0,\qquad
--   (Q_1,\ldots,Q_r)A_{\mathfrak m_v}=J_s(c)A_{\mathfrak m_v},\qquad
--   \det\left(\frac{\partial Q_j}{\partial X_{e_i}}(v)\right)_{1\le i,j\le r}\ne0.
--   $$
--   The local equations and the chosen minor may depend on both $c$ and $v$.
--
--   **Formalization Note.** This is an auxiliary synthesis of generic mixed transversality and local Jacobian presentations, not a verbatim numbered source theorem. The equality is between the actual localized ideals; global ideal generation is not asserted. It includes the affine scaling directions of the punctured multicone. Coefficient rows have entries in every block, although each mixed equation uses only its selected block. Empty sections and zero-length lists are allowed; the empty determinant is one.
--
--   **Reduction.** A checked local-algebra construction reduces this statement to [regular point-local quotients of generic mixed sections](https://prove2.me/theorems/648687d4-3710-4e11-b973-e9ec865463a2). It chooses equations whose gradients form a basis, proves equality with the actual localized ideal by conormal injectivity and Nakayama, and selects distinct coordinate variables with a nonzero Jacobian minor. The geometric construction of the generic regular family remains Open.
-- source:
--   Philippon, Lemmes de zeros dans les groupes algebriques commutatifs, Bull. SMF 114 (1986), pp.363–364, Lemma 3.1 and the mixed-section paragraph, https://numdam.org/articles/10.24033/bsmf.2060/ . S. L. Kleiman, The transversality of a general translate, Compositio Mathematica 28 (1974), Theorem 2(i),(ii), p.290, and Corollary 4(i),(ii), p.291, https://numdam.org/item/CM_1974__28_3_287_0.pdf . The local presentation criterion is related to Stacks Project, Example 10.137.7, Tag 00T8, https://stacks.math.columbia.edu/tag/00T8 . Auxiliary synthesis: generic proper and transverse mixed intersection, avoidance of the boundary and singular locus, transfer to a principal open in coefficient space, and construction of local equations with an invertible minor for the actual multicone ideal remain Open here. The sufficient Jacobian criterion and its transfer to the actual localized quotient are proved in the parent reduction; no global presentation or converse criterion is assumed proved by that reduction.

import Mathlib
import Definitions.Def_PhilipponMultiplicity_GeometricSupport
import Definitions.Def_PhilipponMultiplicity_MixedFlagParameters
set_option autoImplicit false
open scoped BigOperators Topology

namespace PhilipponMultiplicity
open SectionThree SectionThreeSupport

theorem exists_principal_open_mixed_jacobian_presentations
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
                ∃ (r : ℕ) (Q : Fin r → M.CoordinateRing) (e : Fin r ↪ M.Variable),
                  (∀ i, MvPolynomial.eval v (Q i) = 0) ∧
                  (Ideal.span (Set.range Q)).map
                      (algebraMap M.CoordinateRing
                        (Localization.AtPrime (MvPolynomial.vanishingIdeal K {v}))) =
                    (MixedFlag.ideal M (M.vanishingIdeal W) l c l.length).map
                      (algebraMap M.CoordinateRing
                        (Localization.AtPrime (MvPolynomial.vanishingIdeal K {v}))) ∧
                  MvPolynomial.eval v
                    (Matrix.of (fun i j : Fin r => MvPolynomial.pderiv (e i) (Q j))).det ≠ 0) := by sorry

end PhilipponMultiplicity
