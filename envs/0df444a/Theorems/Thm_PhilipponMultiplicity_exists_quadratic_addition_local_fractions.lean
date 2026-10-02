-- Prove2me | Theorems.Thm_PhilipponMultiplicity_exists_quadratic_addition_local_fractions
-- name    : PhilipponMultiplicity.exists_quadratic_addition_local_fractions
-- status  : Open
-- author  : @tomasz
-- created : 2026-10-01T21:29:20.107438+00:00
-- url     : https://prove2.me/theorems/494595e1-9242-4ff1-a521-999e2b03009a
-- title:
--   Lange reembedding with quadratic rational parameter formulas
-- statement:
--   Let $K$ be algebraically closed of characteristic zero and let $E$ be a connected commutative algebraic group. There is a projective realization $F\subseteq\mathbf P^N$ and a group isomorphism $E\to F$ regular in both directions with the following property.
--
--   Every pair $(x,y)\in F\times F$ has an open neighborhood $U$ and indices $c_0,c_1$ such that the corresponding coordinates in the two input blocks are nonzero throughout $U$. Write $\widehat X=X/X_{c_0}$ and $\widehat Y=Y/Y_{c_1}$ for the normalized coordinates. There are finitely many polynomials $A_{t\ell}(X,Y)$ and $B_{t\ell}(Y)$, indexed by $0\le t\le N$ and $0\le\ell<r$, such that each $A_{t\ell}$ has degree at most two in $X$, each $B_{t\ell}$ is independent of $X$, and all denominators are nonzero on $U$. Put
--   $$
--   R_t(\widehat X,\widehat Y)=\sum_{\ell<r}
--   \frac{A_{t\ell}(\widehat X,\widehat Y)}{B_{t\ell}(\widehat Y)}.
--   $$
--   Throughout $U$, the tuple $(R_0,\ldots,R_N)$ is nonzero and
--   $$
--   [R_0(\widehat X,\widehat Y):\cdots:R_N(\widehat X,\widehat Y)]=x+y.
--   $$
--   The first block is the point being translated and the second is the translation parameter. There is no homogeneity condition and no bound on degrees in the parameter.
--
--   **Formalization Note.** The denominators are stored in the two-block polynomial ring with first-block degree zero. Nonvanishing is required at every point of the chosen neighborhood, not only at its center. The topology is the induced multiprojective polynomial Zariski topology. This auxiliary affine-chart formulation of the rational coefficients preceding Rovelli Corollary 3.3.4 is not a verbatim numbered theorem. Constructing the regular reembedding, refining the charts, and producing the local rational families remain Open. Zero-dimensional groups are included. The separate checked reduction clears all denominators without increasing the first-block degree.
-- source:
--   L. Rovelli, Explicit equivariant compactification and Riemann-Roch for algebraic groups, ETH dissertation 14704 (2002), definition of families of translations and Theorem 3.3.2, pp. 63–64; rational-coefficient paragraph before Corollary 3.3.4, p. 66; Theorems 3.4.5–3.4.6(2), p. 72; base-field conventions, p. 13. https://doi.org/10.3929/ethz-a-004445245 ; https://www.research-collection.ethz.ch/bitstreams/63ac9c62-da67-437e-9dcb-413054fb5550/download . See also H. Lange, Families of translations of commutative algebraic groups, Journal of Algebra 109(1) (1987), 260–265, DOI 10.1016/0021-8693(87)90174-8. Auxiliary local affine formulation of rational parameter coefficients in quadratic translation forms, restricted to the group with the coordinate blocks reordered. The geometric construction and its translation to this embedded-group interface remain Open; the algebraic common-denominator reduction is proved separately.

import Definitions.Def_PhilipponMultiplicity_AdditionLaws
import Definitions.Def_PhilipponMultiplicity_Support
set_option autoImplicit false
open scoped BigOperators Topology

namespace PhilipponMultiplicity

theorem exists_quadratic_addition_local_fractions
    (K : Type*) [Field K] [IsAlgClosed K] [CharZero K] :
    ∀ (E : EmbeddedCommutativeGroup K),
      @_root_.IsConnected _ (singleGroupProduct E).zariskiTopology Set.univ →
      ∃ F : EmbeddedCommutativeGroup K, Nonempty (AlgebraicReembedding E F) ∧
        ∀ x y : F.Point, ∃ U : Set (F.Point × F.Point),
          @IsOpen _ (TopologicalSpace.induced (fun xy => F.additionPair xy.1 xy.2)
            (projectiveSquare K F.ambientDimension).zariskiTopology) U ∧
          (x,y) ∈ U ∧
          ∃ c : (projectiveSquare K F.ambientDimension).FactorIndex →
              Fin (F.ambientDimension+1),
          (∀ xy ∈ U, ∀ i : (projectiveSquare K F.ambientDimension).FactorIndex,
            (projectiveSquare K F.ambientDimension).coordinate
              (F.additionPair xy.1 xy.2) ⟨i,c i⟩ ≠ 0) ∧
          ∃ (r : ℕ) (A B : Fin (F.ambientDimension+1) → Fin r →
              (projectiveSquare K F.ambientDimension).CoordinateRing),
          (∀ t a, ∀ m ∈ (A t a).support,
            (∑ k : Fin (F.ambientDimension+1), m ⟨(0 : Fin 2),k⟩) ≤ 2) ∧
          (∀ t a, ∀ m ∈ (B t a).support,
            (∑ k : Fin (F.ambientDimension+1), m ⟨(0 : Fin 2),k⟩) = 0) ∧
          ∀ xy ∈ U,
            let v : (projectiveSquare K F.ambientDimension).Variable → K :=
              fun w =>
                (projectiveSquare K F.ambientDimension).coordinate (F.additionPair xy.1 xy.2) w /
                (projectiveSquare K F.ambientDimension).coordinate (F.additionPair xy.1 xy.2)
                  ⟨w.1,c w.1⟩
            (∀ t a, MvPolynomial.eval v (B t a) ≠ 0) ∧
            ∃ h : (fun t => ∑ a, MvPolynomial.eval v (A t a) /
                MvPolynomial.eval v (B t a)) ≠ 0,
              Projectivization.mk K (fun t => ∑ a, MvPolynomial.eval v (A t a) /
                MvPolynomial.eval v (B t a)) h = (xy.1+xy.2).val := by sorry

end PhilipponMultiplicity
