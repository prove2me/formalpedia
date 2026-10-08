-- Prove2me | Theorems.Thm_PhilipponMultiplicity_exists_principal_open_pointwise_smooth_mixed_zero_locus
-- name    : PhilipponMultiplicity.exists_principal_open_pointwise_smooth_mixed_zero_locus
-- status  : Open
-- author  : @tomasz
-- created : 2026-10-05T12:37:03.284234+00:00
-- url     : https://prove2.me/theorems/3eb62035-89d4-426d-b282-9ea5c1b08da6
-- title:
--   A principal open family of mixed sections smooth at every ordinary point
-- statement:
--   Let $K$ be a Philippon base field and $M=\prod_i\mathbf P^{n_i}$ the given finite multiprojective space. Let $W\subseteq M$ be closed and irreducible. Choose integers $0\leq\alpha_i\leq n_i$ with $\sum_i\alpha_i=\dim W$, and a closed subset $B\subseteq W$ with $W\setminus B\ne\varnothing$.
--
--   Fix an ordered list $l=(i_0,\ldots,i_{s-1})$ in which each block $i$ occurs $\alpha_i$ times. For coefficients $c$, set
--   $$
--   P_j(c)=\sum_{t=0}^{n_{i_j}}c_{j,(i_j,t)}X_{i_j,t},\quad
--   J_s(c)=I(W)+(P_0(c),\ldots,P_{s-1}(c))\subseteq A,
--   $$
--   where $A=K[X_{i,t}]$ is the multihomogeneous coordinate ring. Write $Z(c)$ for the common zero set of the $P_j(c)$ on $W$.
--
--   There is a nonzero polynomial $F$ in the coefficient entries such that whenever $F(c)\ne0$, the set $Z(c)$ is finite and disjoint from $B$. Moreover, for every coordinate tuple $v$ with each block nonzero and satisfying every polynomial in $J_s(c)$, let $\mathfrak m_v=\{P\in A:P(v)=0\}$. Then
--   $$
--   A_{\mathfrak m_v}/J_s(c)A_{\mathfrak m_v}
--   \quad\text{is formally smooth over }K.
--   $$
--   This supplies the pointwise geometric input for a smooth mixed section, retaining all affine scaling directions. Empty sections and zero-length lists are allowed.
--
--   **Formalization Note.** This is an auxiliary coefficient-space formulation of generic transversality, not a verbatim theorem of the cited sources. Formal smoothness is asserted for the actual localized quotient, which need not itself be a finitely presented $K$-algebra. Rows of $c$ contain all block coordinates, but each equation uses only its selected block. No hypothesis about arbitrary nonclosed primes is part of this statement.
--
--   **Reduction.** A checked sufficient Jacobian criterion reduces this statement to [local equations for generic mixed sections](https://prove2.me/theorems/f4809fcb-0a9b-4823-b61a-1b63c83afec1). That input asks for polynomials generating the actual mixed ideal after localization at each ordinary point, with a nonvanishing derivative minor. The local algebra implication is proved; construction of the generic section and these local presentations remains Open.
-- source:
--   Philippon, Lemmes de zeros dans les groupes algebriques commutatifs, Bull. SMF 114 (1986), pp.363–364, Lemma 3.1 and the mixed-section paragraph, https://numdam.org/articles/10.24033/bsmf.2060/ . S. L. Kleiman, The transversality of a general translate, Compositio Mathematica 28 (1974), Theorem 2(i),(ii), p.290, and Corollary 4(i),(ii), p.291, https://numdam.org/item/CM_1974__28_3_287_0.pdf . Auxiliary synthesis, not a verbatim source theorem: the remaining geometry is generic proper intersection away from the boundary and singular locus, transverse intersection on the regular locus, transfer to affine coefficient space, and comparison with the actual point-local multicone quotient. The separate Jacobson/Nullstellensatz argument that extends pointwise smoothness to arbitrary punctured primes is proved in the parent reduction and is not an obligation of this child.

import Mathlib
import Definitions.Def_PhilipponMultiplicity_GeometricSupport
import Definitions.Def_PhilipponMultiplicity_MixedFlagParameters
set_option autoImplicit false
open scoped BigOperators Topology

namespace PhilipponMultiplicity
open SectionThree SectionThreeSupport

theorem exists_principal_open_pointwise_smooth_mixed_zero_locus
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
                Algebra.FormallySmooth K
                  ((Localization.AtPrime (MvPolynomial.vanishingIdeal K {v})) ⧸
                    (MixedFlag.ideal M (M.vanishingIdeal W) l c l.length).map
                      (algebraMap M.CoordinateRing
                        (Localization.AtPrime (MvPolynomial.vanishingIdeal K {v}))))) := by sorry

end PhilipponMultiplicity
