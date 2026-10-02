-- Prove2me | Theorems.Thm_PhilipponMultiplicity_exists_quadratic_addition_local_cover
-- name    : PhilipponMultiplicity.exists_quadratic_addition_local_cover
-- status  : Open
-- author  : @tomasz
-- created : 2026-10-01T16:14:07.899522+00:00
-- url     : https://prove2.me/theorems/0a636e38-74e5-4e5f-9713-8e2f9e007095
-- title:
--   Lange geometric construction of a local quadratic addition cover
-- statement:
--   Let $K$ be algebraically closed of characteristic zero and let $E$ be a connected commutative algebraic group. There is a projective realization $F\subseteq\mathbf P^N$ and a group isomorphism $E\to F$ regular in both directions, such that every pair $(x,y)\in F\times F$ has an open neighborhood $U$ with a bihomogeneous polynomial tuple $P=(P_0,\ldots,P_N)$ of common bidegree $(d_0,d_1)$ satisfying
--   $$
--   d_0\le2,\qquad P(a,b)\ne0,\qquad [P_0(a,b):\cdots:P_N(a,b)]=a+b
--   \quad\text{for all }(a,b)\in U.
--   $$
--   The first coordinate block is the point being translated. There is no asserted bound on the second-block degree, and different neighborhoods may use different tuples and degrees. This is the local geometric construction underlying quadratic addition laws.
--
--   **Formalization Note.** The open neighborhoods use the induced multiprojective polynomial Zariski topology on the algebraic pair variety. This formulation restricts Rovelli's local-formula conclusion to the group inside its completion and reorders the coordinate blocks. It imposes neither global compatibility outside $U$ nor an extra irreducibility hypothesis. Zero-dimensional groups are included. Constructing the reembedding and its local tuples in the existing embedded-group interface remains Open.
--
--
--   **Verified homogenization reduction.** The accepted sketch explicitly pads each affine monomial with powers of the chosen chart coordinates, producing a common bihomogeneous degree $(2,B)$. It proves that normalized evaluation is unchanged and that arbitrary nonzero chart lifts multiply the whole output tuple by one common nonzero scalar. The tuple therefore remains nonzero and represents the same sum.
--
--   The sole Open dependency is [Lange reembedding with local affine quadratic addition formulas](https://prove2.me/theorems/633773f5-699a-4558-afea-c7412fa81b1d). It supplies the reembedding, coordinate-chart neighborhoods, and affine formulas quadratic in the first block. No homogeneous or common-degree condition is assumed there. The geometric construction remains Open; the algebraic passage from affine to bihomogeneous formulas is proved.
-- source:
--   H. Lange, Families of translations of commutative algebraic groups, Journal of Algebra 109(1) (1987), pp. 260–265, DOI 10.1016/0021-8693(87)90174-8. L. Rovelli, Explicit equivariant compactification and Riemann-Roch for algebraic groups, ETH dissertation 14704 (2002), Corollary 3.3.4, p. 66; Theorems 3.4.5 and 3.4.6(2), p. 72; base-field and connectedness conventions, p. 13. https://doi.org/10.3929/ethz-a-004445245 ; https://www.research-collection.ethz.ch/bitstreams/63ac9c62-da67-437e-9dcb-413054fb5550/download . Local-formula consequence restricted to the commutative group, with coordinate blocks reordered so the translated point is first. No compatibility outside the chosen open neighborhood is part of this assertion.

import Definitions.Def_PhilipponMultiplicity_AdditionLaws
import Definitions.Def_PhilipponMultiplicity_Support
set_option autoImplicit false
open scoped BigOperators Topology

namespace PhilipponMultiplicity

theorem exists_quadratic_addition_local_cover
    (K : Type*) [Field K] [IsAlgClosed K] [CharZero K] :
    ∀ (E : EmbeddedCommutativeGroup K),
      @_root_.IsConnected _ (singleGroupProduct E).zariskiTopology Set.univ →
      ∃ F : EmbeddedCommutativeGroup K, Nonempty (AlgebraicReembedding E F) ∧
        ∀ x y : F.Point, ∃ U : Set (F.Point × F.Point),
          @IsOpen _ (TopologicalSpace.induced (fun xy => F.additionPair xy.1 xy.2)
            (projectiveSquare K F.ambientDimension).zariskiTopology) U ∧
          (x,y) ∈ U ∧
          ∃ D : (projectiveSquare K F.ambientDimension).FactorIndex → ℕ,
          ∃ P : Fin (F.ambientDimension+1) →
            (projectiveSquare K F.ambientDimension).CoordinateRing,
          D (0 : Fin 2) ≤ 2 ∧
          (∀ j, (projectiveSquare K F.ambientDimension).IsHomogeneous (P j) D) ∧
          ∀ xy ∈ U, ∃ h :
            (fun j => (projectiveSquare K F.ambientDimension).eval (P j)
              (F.additionPair xy.1 xy.2)) ≠ 0,
            Projectivization.mk K (fun j => (projectiveSquare K F.ambientDimension).eval
              (P j) (F.additionPair xy.1 xy.2)) h = (xy.1+xy.2).val := by sorry

end PhilipponMultiplicity
