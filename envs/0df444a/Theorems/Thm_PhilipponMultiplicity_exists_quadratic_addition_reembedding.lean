-- Prove2me | Theorems.Thm_PhilipponMultiplicity_exists_quadratic_addition_reembedding
-- name    : PhilipponMultiplicity.exists_quadratic_addition_reembedding
-- status  : Open
-- author  : @tomasz
-- created : 2026-09-30T16:11:34.975987+00:00
-- url     : https://prove2.me/theorems/5d8d20ad-2e39-413f-aeab-effa7b57c850
-- title:
--   Lange reembedding with covering quadratic addition laws
-- statement:
--   Let $K$ be an algebraically closed field of characteristic zero and let $E$ be a connected commutative algebraic group. There is an algebraically isomorphic projective realization $F$ admitting a covering family of bihomogeneous addition laws.
--
--   Each law is a tuple of homogeneous polynomials in two blocks of projective coordinates. The first block represents the point being translated; its degree is at most two. There is no asserted bound on the second-block degree. Wherever the tuple is nonzero, it represents the group sum. For every pair of points of $F$, at least one such tuple is nonzero.
--
--   **Formalization Note.** The reembedding is regular in both directions. The accepted sketch proves that any homogeneous tuple representing a regular map on a nonempty open subset of an irreducible domain represents it on its entire nonzero locus. This supplies the global compatibility of each addition law without changing its bidegree. The proof uses closed equalizers of regular projective maps, rather than a Hausdorff assumption on a Zariski space.
--
--   The sole Open dependency is [Lange reembedding with local quadratic addition formulas](https://prove2.me/theorems/ef92e04f-d5b1-4ae9-a945-61205dc29e75). It supplies the geometric reembedding, irreducibility of the algebraic group-pair variety, and local formulas covering all pairs. The topology on pairs is the actual induced multiprojective Zariski topology. The geometric construction remains Open; the local-to-global implication is proved.
-- source:
--   H. Lange, Families of translations of commutative algebraic groups, Journal of Algebra 109(1) (1987), pp. 260–265, DOI 10.1016/0021-8693(87)90174-8. Algebraic formulation: L. Rovelli, Explicit equivariant compactification and Riemann-Roch for algebraic groups, ETH dissertation 14704 (2002), Corollary 3.3.4, p. 66, and Theorem 3.4.6(2), p. 72; base-field convention on p. 13. https://doi.org/10.3929/ethz-a-004445245 . The formal statement restricts to commutative groups, puts the translated point in the first block, and includes the global compatibility of each rational addition law.

import Definitions.Def_PhilipponMultiplicity_AdditionLaws
import Definitions.Def_PhilipponMultiplicity_Support

set_option autoImplicit false
open scoped BigOperators Topology

namespace PhilipponMultiplicity

theorem exists_quadratic_addition_reembedding
    (K : Type*) [Field K] [IsAlgClosed K] [CharZero K]
    (E : EmbeddedCommutativeGroup K)
    (hconnected : @_root_.IsConnected _ (singleGroupProduct E).zariskiTopology Set.univ) :
    ∃ F : EmbeddedCommutativeGroup K, Nonempty (AlgebraicReembedding E F) ∧
      ∀ x y : F.Point, ∃ law : F.AdditionLaw,
        law.degree (0 : Fin 2) ≤ 2 ∧
        (fun j => (projectiveSquare K F.ambientDimension).eval (law.coordinates j)
          (F.additionPair x y)) ≠ 0 := by sorry

end PhilipponMultiplicity
