-- Prove2me | Theorems.Thm_PhilipponMultiplicity_exists_quadratic_local_addition_reembedding
-- name    : PhilipponMultiplicity.exists_quadratic_local_addition_reembedding
-- status  : Open
-- author  : @tomasz
-- created : 2026-10-01T15:56:14.682738+00:00
-- url     : https://prove2.me/theorems/ef92e04f-d5b1-4ae9-a945-61205dc29e75
-- title:
--   Lange reembedding with local quadratic addition formulas
-- statement:
--   Let $K$ be algebraically closed of characteristic zero, and let $E$ be a connected commutative algebraic group. There is a projective realization $F\subseteq\mathbf P^N$ and a group isomorphism $E\to F$ regular in both directions, with the following properties.
--
--   The pair variety $F\times F$ is irreducible. Every pair $(x,y)$ has a Zariski-open neighborhood $U\subseteq F\times F$ and a tuple of bihomogeneous polynomials $P_0,\ldots,P_N$ of common bidegree $(d_0,d_1)$ such that
--   $$
--   d_0\le 2,\qquad P(a,b)\ne0,\qquad [P_0(a,b):\cdots:P_N(a,b)]=a+b
--   \quad ((a,b)\in U).
--   $$
--   The first coordinate block is the point being translated; no bound is asserted on $d_1$. This provides the geometric input for constructing globally compatible quadratic addition laws.
--
--   **Formalization Note.** The accepted sketch proves irreducibility of the algebraic pair variety from connectedness and regular reembedding. It uses the actual induced multiprojective Zariski topology. A general theorem derives pair irreducibility from irreducible factors and continuous coordinate slices; it does not require identifying this topology with a product topology.
--
--   The sole Open dependency is [Lange's geometric construction of a local quadratic addition cover](https://prove2.me/theorems/0a636e38-74e5-4e5f-9713-8e2f9e007095). It asks for the regular reembedding and the local tuples only. Connectedness transfer and pair irreducibility are proved, including zero-dimensional groups. The geometric construction of the local cover remains Open.
-- source:
--   H. Lange, Families of translations of commutative algebraic groups, Journal of Algebra 109(1) (1987), pp. 260–265, DOI 10.1016/0021-8693(87)90174-8. L. Rovelli, Explicit equivariant compactification and Riemann-Roch for algebraic groups, ETH dissertation 14704 (2002), Corollary 3.3.4, p. 66; Theorems 3.4.5 and 3.4.6(2), p. 72; algebraically closed characteristic-zero base-field and connected/irreducible conventions, p. 13. https://doi.org/10.3929/ethz-a-004445245 ; full text https://www.research-collection.ethz.ch/bitstreams/63ac9c62-da67-437e-9dcb-413054fb5550/download . Auxiliary consequence, with the group restricted to the commutative case and the coordinate blocks reordered to put the translated point first. Irreducibility of the algebraic group product is recorded explicitly; the assertion concerns its algebraic Zariski topology.

import Definitions.Def_PhilipponMultiplicity_AdditionLaws
import Definitions.Def_PhilipponMultiplicity_Support
set_option autoImplicit false
open scoped BigOperators Topology

namespace PhilipponMultiplicity

theorem exists_quadratic_local_addition_reembedding
    (K : Type*) [Field K] [IsAlgClosed K] [CharZero K] :
    ∀ (E : EmbeddedCommutativeGroup K),
      @_root_.IsConnected _ (singleGroupProduct E).zariskiTopology Set.univ →
      ∃ F : EmbeddedCommutativeGroup K, Nonempty (AlgebraicReembedding E F) ∧
        @IsPreirreducible (F.Point × F.Point)
          (TopologicalSpace.induced (fun xy => F.additionPair xy.1 xy.2)
            (projectiveSquare K F.ambientDimension).zariskiTopology) Set.univ ∧
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
