-- Prove2me | Theorems.Thm_PCSFBreach_Main_theorem_2
-- name    : PCSFBreach.Main.theorem_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:57:07.219638+00:00
-- url     : https://prove2.me/theorems/8fda2239-9bcf-4af8-a14d-ed5070257668
-- title:
--   Theorem 2 (Bifactor Algorithm) — cost ≤ (2 − 10⁻¹⁸)·c(F) + (10⁶ + 2)·π(D̄(F)) for every forest F
-- statement:
--   Let $\delta=10^{-18}$ and $K=10^6+2$. There is one polynomial-time computable function $M$ such that for every PCSF instance $J$ with nonnegative rational data, $M$ maps the code of $J$ to the code of a forest $F$ of $J$ with
--   $$\mathrm{cost}(F)\le(2-\delta)\cdot c(F')+K\cdot\pi(\bar D(F'))\qquad\text{for every forest }F'\text{ of }J .$$
--
--   The bifactor algorithm pays a factor below 2 on the edge cost of any comparison forest at the price of a large constant factor on its penalties; it is the third candidate of Algorithm 1 (Lemma 5).
--
--   Differences from the source:
--   - generalization: an undirected graph G = (V, E) and a set D of pairs {s_i, t_i} → an edge list on the vertex set Fin n (parallel edges and loops allowed) and a pair list (repeated pairs and s_i = t_i allowed); reason: covers more instances: a simple graph with a set of distinct pairs is the case of lists without loops, parallel edges or repeats; a loop never lies in a forest and a pair with s_i = t_i is always connected
--   - encoding: a polynomial-time algorithm on (G, c, D, π) → one function M on binary strings with PolyTimeComputable M (published QAlgorithms_ClassicalStringComputability: Mathlib multi-stack Turing machine, time polynomial in the input length), fixed before the instance, mapping the binary code encInst J of every instance J with nonnegative rational costs and penalties to the characteristic vector encEdgeSet of its output edge set; reason: bit model; Appendix B (p. 47) assumes rational input data; the vertex count n is coded in unary (the input graph G = (V, E) lists its vertices) and every other number in binary, so the time bound is polynomial in |V| plus the bit length of the data; strings that code no instance are unconstrained
--   - encoding: a solution → an edge set F that is a forest of the instance (IsForest: no loop, no edge joining two vertices already connected by the other edges of F); reason: p. 1: a feasible solution is any forest F ⊆ E
--   - reading: there exists an efficient algorithm → one deterministic PolyTimeComputable function; reason: the algorithm of §8 is deterministic once Remark 1 derandomizes the LP-pruning step
-- source:
--   Bosch-Calvo, Grandoni, Mátravölgyi, Breaching the 2-Approximation Barrier for Prize-Collecting Steiner Forest, STOC 2027 submission (manuscript sha256 05d9cc28…3eb3), p. 7, Theorem 2 (restated p. 12; proved as Theorem 3, pp. 32–44)

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_PCSFBreach_Main_Instance
import Definitions.Def_PCSFBreach_Main_Encoding
open QAlgorithms.Complexity

namespace PCSFBreach.Main

/-- Theorem 2 (Bifactor Algorithm, p. 7): one polynomial-time algorithm computes a solution of cost
at most `(2 − δ) · c(F) + K · π(D̄(F))` for every forest `F`, with `δ = 10⁻¹⁸`, `K = 10⁶ + 2`. -/
theorem theorem_2 :
    ∃ M : Str → Str, PolyTimeComputable M ∧
      ∀ J : RatInstance, ∃ F : Finset J.toInstance.Edge,
        M (encInst J) = encEdgeSet J.toInstance F ∧ J.toInstance.IsForest F ∧
          ∀ F' : Finset J.toInstance.Edge, J.toInstance.IsForest F' →
            J.toInstance.cost F ≤ (2 - 1 / 10 ^ 18) * J.toInstance.edgeCost F'
              + (10 ^ 6 + 2) * J.toInstance.penaltyOf (J.toInstance.disconnectedPairs F') := by sorry

end PCSFBreach.Main
