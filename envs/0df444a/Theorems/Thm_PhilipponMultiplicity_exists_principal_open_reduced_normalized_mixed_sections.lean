-- Prove2me | Theorems.Thm_PhilipponMultiplicity_exists_principal_open_reduced_normalized_mixed_sections
-- name    : PhilipponMultiplicity.exists_principal_open_reduced_normalized_mixed_sections
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-08T20:29:52.719984+00:00
-- url     : https://prove2.me/theorems/a3a12c71-04e6-47df-b863-6383d307a7c9
-- title:
--   Generic mixed sections have radical normalized affine chart ideals
-- statement:
--   Let $K$ be a Philippon base field and $M=\prod_i\mathbf P^{n_i}$. Let $W\subseteq M$ be closed and irreducible. Choose $0\le\alpha_i\le n_i$ with $\sum_i\alpha_i=\dim W$, where dimension is the total degree of the actual quotient Hilbert polynomial. Let $B\subseteq W$ be closed with $W\setminus B\ne\varnothing$, and let $l$ be an ordered list in which each block $i$ occurs $\alpha_i$ times.
--
--   For coefficient arrays $c$, let $P_j(c)$ be the block-linear polynomial specified by row $j$, let $I(c)=I(W)+(P_j(c):j<|l|)$, and let $Z(c)$ be the common zero set in $W$. There exists a nonzero polynomial $F$ in all coefficient entries such that $F(c)\ne0$ implies that $Z(c)$ is finite, disjoint from $B$, and, for every choice of a pivot $b_i\in\{0,\ldots,n_i\}$ in each block, the ideal
--   $$
--   I(c)+(X_{i,b_i}-1:i)
--   $$
--   in the original polynomial coordinate ring is radical.
--
--   Thus every normalized affine chart of the actual mixed-section scheme is reduced. The zero quotient ring and empty sections are allowed, as are zero-length cutting lists. Coefficients outside a row's selected block are unused.
--
--   **Formalization Note.** This is an auxiliary coefficient-space and affine-chart formulation of generic proper reduced mixed intersection, not a verbatim theorem from the cited sources. The normalization equations are added to the actual cutting ideal; the claim is stronger than reducedness of the set of points. Generic finiteness, boundary avoidance, a nonzero principal-open coefficient condition, and comparison with the concrete multiprojective model remain to be proved. The parent reduction proves the transfer from these normalized chart ideals to radicality of the original homogeneous ideal at all nonzero-block representatives.
--
--   **Verified Jacobian reduction (8 October 2026).** It suffices to prove [generic full-rank pointwise Jacobians in the normalized chart ideals](https://prove2.me/theorems/a9b9ed86-6b3e-443d-9c74-a648242f5ae1), together with the boundary avoidance included there. The new proof shows that such Jacobian determinants annihilate the quotient's differential module, uses the weak Nullstellensatz to prove that module vanishes, and derives radicality and finite-dimensionality of the actual coordinate quotient. An injective normalized-coordinate map on each of finitely many projective charts then proves finiteness of the mixed section. Thus the new Open child assumes neither radicality nor finiteness. Generic transversality and its concrete coefficient-space and chart comparisons remain Open; the original formal statement is unchanged.
-- source:
--   P. Philippon, Lemmes de zeros dans les groupes algebriques commutatifs, Bull. SMF 114 (1986), pp.363–364, Lemma 3.1 and the mixed-section paragraph, https://numdam.org/articles/10.24033/bsmf.2060/ . S. L. Kleiman, The transversality of a general translate, Compositio Mathematica 28 (1974), Theorem 2 and Corollary 4, pp.290–291, and Remark 7, p.292 (the reduced variant), https://numdam.org/item/CM_1974__28_3_287_0.pdf . Auxiliary synthesis: apply generic proper intersection and reducedness to products of projective linear subspaces, avoid the proper boundary, pull back to coefficient space, restrict to a principal open, and identify each normalized affine chart with the quotient by the displayed ideal. These geometric and model comparisons remain Open. The parent proves the homogeneous-local algebraic transfer.

import Mathlib
import Definitions.Def_PhilipponMultiplicity_GeometricSupport
import Definitions.Def_PhilipponMultiplicity_MixedFlagParameters
set_option autoImplicit false
open scoped BigOperators Topology

namespace PhilipponMultiplicity
open SectionThree SectionThreeSupport

theorem exists_principal_open_reduced_normalized_mixed_sections
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
            (∀ b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1),
              (MixedFlag.ideal M (M.vanishingIdeal W) l c l.length ⊔
                Ideal.span (Set.range (fun i : M.FactorIndex =>
                  (MvPolynomial.X (⟨i,b i⟩ : M.Variable) : M.CoordinateRing) - 1))).IsRadical) := by sorry

end PhilipponMultiplicity
