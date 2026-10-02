-- Prove2me | Theorems.Thm_PhilipponMultiplicity_exists_quadratic_affine_addition_local_cover
-- name    : PhilipponMultiplicity.exists_quadratic_affine_addition_local_cover
-- status  : Open
-- author  : @tomasz
-- created : 2026-10-01T18:33:55.364+00:00
-- url     : https://prove2.me/theorems/633773f5-699a-4558-afea-c7412fa81b1d
-- title:
--   Lange reembedding with local affine quadratic addition formulas
-- statement:
--   Let $K$ be algebraically closed of characteristic zero and let $E$ be a connected commutative algebraic group. There is a projective realization $F\subseteq\mathbf P^N$ and a group isomorphism $E\to F$ regular in both directions with the following property.
--
--   Every pair $(x,y)\in F\times F$ has an open neighborhood $U$ and indices $c_0,c_1\in\{0,\ldots,N\}$ such that the corresponding coordinates in the two input blocks are nonzero everywhere on $U$. Write $\widehat X=X/X_{c_0}$ and $\widehat Y=Y/Y_{c_1}$ for the normalized coordinates. There are ordinary polynomials $Q_0,\ldots,Q_N\in K[X_0,\ldots,X_N,Y_0,\ldots,Y_N]$, each of degree at most two in the first block, such that on $U$ their normalized evaluation is a nonzero tuple and
--   $$
--   [Q_0(\widehat X,\widehat Y):\cdots:Q_N(\widehat X,\widehat Y)]=x+y.
--   $$
--   There is no homogeneity requirement, no common-degree requirement, and no bound on the second-block degree. The first block is the point being translated; the second is the translation parameter.
--
--   **Formalization Note.** The neighborhoods use the induced multiprojective polynomial Zariski topology. This is an auxiliary affine-chart consequence of the Lange–Rovelli construction, with the coordinate blocks reordered, rather than a verbatim numbered theorem. Constructing the regular reembedding, refining to the indicated charts, and constructing the affine polynomial formulas remain Open. Zero-dimensional groups are included. The separate homogenization reduction supplies bihomogeneity and a common bidegree without increasing the first-block bound.
--
--
--   **Verified parameter-denominator reduction.** The accepted sketch constructs one common product of all rational parameter denominators and multiplies each numerator by the complementary product. It proves the resulting polynomial tuple has the same first-block degree bound and differs from the rational tuple by one common nonzero scalar on the same neighborhood.
--
--   The sole Open dependency is [quadratic rational parameter formulas](https://prove2.me/theorems/494595e1-9242-4ff1-a521-999e2b03009a). It supplies the reembedding, chart neighborhoods, and local formulas as finite sums of fractions with parameter-only denominators nonzero throughout each neighborhood. Geometric construction of these families remains Open; clearing their denominators and preserving their projective values are proved.
-- source:
--   H. Lange, Families of translations of commutative algebraic groups, Journal of Algebra 109(1) (1987), pp. 260–265, DOI 10.1016/0021-8693(87)90174-8. L. Rovelli, Explicit equivariant compactification and Riemann-Roch for algebraic groups, ETH dissertation 14704 (2002), Corollary 3.3.4, p. 66; Theorems 3.4.5 and 3.4.6(2), p. 72; base-field and connectedness conventions, p. 13. https://doi.org/10.3929/ethz-a-004445245 ; https://www.research-collection.ethz.ch/bitstreams/63ac9c62-da67-437e-9dcb-413054fb5550/download . Local-formula consequence restricted to the commutative group, with coordinate blocks reordered so the translated point is first. No compatibility outside the chosen open neighborhood is part of this assertion. Auxiliary affine-chart formulation of the discussion preceding Rovelli Corollary 3.3.4 on p. 66 and the embedding construction of Theorems 3.4.5–3.4.6 on p. 72. Geometric reembedding, chart refinement, and affine formula construction are included in this Open assertion; the separate reduction proves monomial homogenization and common-scalar invariance.

import Definitions.Def_PhilipponMultiplicity_AdditionLaws
import Definitions.Def_PhilipponMultiplicity_Support
set_option autoImplicit false
open scoped BigOperators Topology

namespace PhilipponMultiplicity

theorem exists_quadratic_affine_addition_local_cover
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
          ∃ Q : Fin (F.ambientDimension+1) →
            (projectiveSquare K F.ambientDimension).CoordinateRing,
          (∀ t, ∀ m ∈ (Q t).support,
            (∑ k : Fin (F.ambientDimension+1), m ⟨(0 : Fin 2),k⟩) ≤ 2) ∧
          ∀ xy ∈ U, ∃ h :
            (fun t => MvPolynomial.eval
              (fun v : (projectiveSquare K F.ambientDimension).Variable =>
                (projectiveSquare K F.ambientDimension).coordinate (F.additionPair xy.1 xy.2) v /
                (projectiveSquare K F.ambientDimension).coordinate (F.additionPair xy.1 xy.2)
                  ⟨v.1,c v.1⟩) (Q t)) ≠ 0,
            Projectivization.mk K (fun t => MvPolynomial.eval
              (fun v : (projectiveSquare K F.ambientDimension).Variable =>
                (projectiveSquare K F.ambientDimension).coordinate (F.additionPair xy.1 xy.2) v /
                (projectiveSquare K F.ambientDimension).coordinate (F.additionPair xy.1 xy.2)
                  ⟨v.1,c v.1⟩) (Q t)) h = (xy.1+xy.2).val := by sorry

end PhilipponMultiplicity
