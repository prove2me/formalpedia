-- Prove2me | Theorems.Thm_PhilipponMultiplicity_exists_principal_open_smooth_mixed_flag_family
-- name    : PhilipponMultiplicity.exists_principal_open_smooth_mixed_flag_family
-- status  : Open
-- author  : @tomasz
-- created : 2026-10-04T20:09:46.180982+00:00
-- url     : https://prove2.me/theorems/cb087b60-bd87-46f8-8672-81234ffb113d
-- title:
--   A principal-open family of smooth mixed linear sections
-- statement:
--   Let $K$ be a Philippon base field and $M=\prod_i\mathbf P^{n_i}$ the nonempty finite product in the mission's multiprojective model. Let $W\subseteq M$ be a nonempty irreducible closed subset, and let $0\leq\alpha_i\leq n_i$ with $\sum_i\alpha_i=\dim W$. Let $B\subseteq W$ be closed with $W\setminus B\ne\varnothing$.
--
--   There is an ordered list $l=(i_0,\ldots,i_{s-1})$ containing each block $i$ exactly $\alpha_i$ times, and a nonzero polynomial $F$ in the entries of an $s$-row coefficient matrix, such that every matrix $c$ with $F(c)\ne0$ has the following properties. Define
--   $$P_j(c)=\sum_{t=0}^{n_{i_j}}c_{j,(i_j,t)}X_{i_j,t},\qquad
--   J_s(c)=I(W)+(P_0(c),\ldots,P_{s-1}(c)).$$
--   Coefficients outside the selected block of a row are unused. There are subspaces $L_i\subseteq K^{n_i+1}$ of codimension $\alpha_i$ for which the mixed section $W\cap\prod_i\mathbf P(L_i)$ is finite, disjoint from $B$, and consists exactly of the points of $W$ where all $P_j(c)$ vanish. At every prime of $A/J_s(c)$ where each coordinate block has a coordinate outside the prime, the quotient is smooth over $K$.
--
--   **Formalization Note.** A checked proof-sketch reduces this statement to [generic finite smooth zero loci for a prescribed block list](https://prove2.me/theorems/56195750-704c-425e-bd66-ab81b390fe02). The construction of subspaces with the required codimensions and their equality with the equation locus is proved. The remaining geometric input, including comparison with the punctured multicone coordinate ring, remains Open. The formulation is an auxiliary synthesis rather than a verbatim theorem of the cited sources. Empty final sections and zero-length lists are allowed.
-- source:
--   Philippon, Lemmes de zeros dans les groupes algebriques commutatifs, Bull. SMF 114 (1986), Lemma 3.1 and the mixed-section paragraph, pp.363–364, https://numdam.org/articles/10.24033/bsmf.2060/ . S. L. Kleiman, The transversality of a general translate, Compositio Mathematica 28 (1974), Theorem 2(i),(ii) p.290 and Corollary 4 p.291, https://numdam.org/item/CM_1974__28_3_287_0.pdf . Auxiliary coefficient-space formulation: generic proper and transverse mixed sections avoid the prescribed boundary and the singular locus; pull back the good open along the full-rank coefficient parametrization and take a nonempty principal open. The punctured multicone is locally a torus product over the section. The existence and coordinate-ring comparison are obligations of this Open lemma.

import Mathlib
import Definitions.Def_PhilipponMultiplicity_GeometricSupport
import Definitions.Def_PhilipponMultiplicity_MixedFlagParameters
set_option autoImplicit false
open scoped BigOperators Topology

namespace PhilipponMultiplicity
open SectionThree SectionThreeSupport

theorem exists_principal_open_smooth_mixed_flag_family
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K) :
    ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ B : Set M.Point, @IsClosed _ M.zariskiTopology B → B ⊆ W →
      (W \ B).Nonempty →
      ∃ l : List M.FactorIndex, (∀ i, l.count i = α i) ∧
        ∃ F : MvPolynomial (Fin l.length × M.Variable) K, F ≠ 0 ∧
          ∀ c : Fin l.length → M.Variable → K,
            MvPolynomial.eval (Function.uncurry c) F ≠ 0 →
            ∃ L : ∀ i : M.FactorIndex, Submodule K (Fin (M.ambientDimension i + 1) → K),
              (∀ i, Module.finrank K (L i) + α i = M.ambientDimension i + 1) ∧
              (linearSlice M W L).Finite ∧ Disjoint (linearSlice M W L) B ∧
              (∀ x : M.Point, x ∈ linearSlice M W L ↔ x ∈ W ∧
                ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c j) x = 0) ∧
              (∀ q : PrimeSpectrum (M.CoordinateRing ⧸
                  MixedFlag.ideal M (M.vanishingIdeal W) l c l.length),
                (∀ i : M.FactorIndex, ∃ j : Fin (M.ambientDimension i + 1),
                  Ideal.Quotient.mk (MixedFlag.ideal M (M.vanishingIdeal W) l c l.length)
                    (MvPolynomial.X ⟨i,j⟩) ∉ q.asIdeal) →
                Algebra.IsSmoothAt K q.asIdeal) := by sorry

end PhilipponMultiplicity
