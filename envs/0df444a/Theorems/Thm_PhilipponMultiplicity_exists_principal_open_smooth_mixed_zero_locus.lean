-- Prove2me | Theorems.Thm_PhilipponMultiplicity_exists_principal_open_smooth_mixed_zero_locus
-- name    : PhilipponMultiplicity.exists_principal_open_smooth_mixed_zero_locus
-- status  : Open
-- author  : @tomasz
-- created : 2026-10-05T00:00:41.575476+00:00
-- url     : https://prove2.me/theorems/56195750-704c-425e-bd66-ab81b390fe02
-- title:
--   Generic mixed equations have a finite smooth zero locus
-- statement:
--   Let $K$ be a Philippon base field, let $M=\prod_i\mathbf P^{n_i}$ be the mission's finite multiprojective space, and let $W\subseteq M$ be closed and irreducible. Choose $0\leq\alpha_i\leq n_i$ with $\sum_i\alpha_i=\dim W$. Let $B\subseteq W$ be closed with $W\setminus B\ne\varnothing$.
--
--   Fix any ordered block list $l=(i_0,\ldots,i_{s-1})$ containing each $i$ exactly $\alpha_i$ times. For a coefficient matrix $c$, define
--   $$
--   P_j(c)=\sum_{t=0}^{n_{i_j}}c_{j,(i_j,t)}X_{i_j,t},\qquad
--   Z(c)=\{x\in W:P_j(c)(x)=0\text{ for all }j<s\},
--   $$
--   and put $J_s(c)=I(W)+(P_0(c),\ldots,P_{s-1}(c))$ in the multihomogeneous coordinate ring $A$.
--
--   There is a nonzero polynomial $F$ in the coefficient entries such that
--   $$
--   F(c)\ne0\quad\Longrightarrow\quad
--   Z(c)\text{ is finite},\quad Z(c)\cap B=\varnothing,
--   $$
--   and $A/J_s(c)$ is smooth over $K$ at every prime at which each coordinate block has a coordinate outside the prime.
--
--   This is a generic geometric zero-locus assertion for a prescribed ordering of the equations. It supplies the geometric input for mixed-section constructions. Empty zero sets and zero-length lists are allowed.
--
--   **Formalization Note.** Coefficient rows contain entries from all blocks, but each equation uses only its selected block. The statement does not specify subspaces or their codimensions. Those are reconstructed by a separately checked determinant and kernel argument. The smoothness assertion concerns the punctured affine multicone, retaining one affine scale per projective block. This auxiliary coefficient-space formulation remains Open.
--
--   A checked reduction now proves that the smoothness clause follows from smoothness of the actual point-local quotients at ordinary nonzero-block tuples. It uses Hilbert’s Nullstellensatz, the Jacobson property, openness of the smooth locus, and a ground-field-compatible quotient/localization equivalence. The remaining [pointwise geometric construction](https://prove2.me/theorems/3eb62035-89d4-426d-b282-9ea5c1b08da6) supplies the principal open family and stays Open.
-- source:
--   Philippon, Lemmes de zeros dans les groupes algebriques commutatifs, Bull. SMF 114 (1986), pp.363–364, Lemma 3.1 and the mixed-section paragraph, https://numdam.org/articles/10.24033/bsmf.2060/ . S. L. Kleiman, The transversality of a general translate, Compositio Mathematica 28 (1974), Theorem 2(i),(ii), p.290, and Corollary 4, p.291, https://numdam.org/item/CM_1974__28_3_287_0.pdf . Auxiliary synthesis, not a verbatim source theorem: generic proper intersections avoid B and the singular locus, and transversality on the regular locus gives a smooth zero-dimensional section. Transfer the good open to affine coefficient space and choose a nonempty principal open. Comparison with the concrete point model and the punctured multicone coordinate ring remain obligations of this child. Codimension of the kernel subspaces is proved separately by explicit nonzero determinant minors and is not assumed here.

import Mathlib
import Definitions.Def_PhilipponMultiplicity_GeometricSupport
import Definitions.Def_PhilipponMultiplicity_MixedFlagParameters
set_option autoImplicit false
open scoped BigOperators Topology

namespace PhilipponMultiplicity
open SectionThree SectionThreeSupport

theorem exists_principal_open_smooth_mixed_zero_locus
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
            (∀ q : PrimeSpectrum (M.CoordinateRing ⧸
                  MixedFlag.ideal M (M.vanishingIdeal W) l c l.length),
                (∀ i : M.FactorIndex, ∃ j : Fin (M.ambientDimension i + 1),
                  Ideal.Quotient.mk (MixedFlag.ideal M (M.vanishingIdeal W) l c l.length)
                    (MvPolynomial.X ⟨i,j⟩) ∉ q.asIdeal) →
                Algebra.IsSmoothAt K q.asIdeal) := by sorry

end PhilipponMultiplicity
