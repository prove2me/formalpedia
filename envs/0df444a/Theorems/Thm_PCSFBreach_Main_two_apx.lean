-- Prove2me | Theorems.Thm_PCSFBreach_Main_two_apx
-- name    : PCSFBreach.Main.two_apx
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:57:00.559454+00:00
-- url     : https://prove2.me/theorems/563362db-f14d-493b-bf74-e5c0a1f08984
-- title:
--   2APX [AGHJM24a] — a polynomial-time 2-approximation for PCSF (cited black box)
-- statement:
--   Ahmadi, Gholami, Hajiaghayi, Jabbarzade and Mahdavi [AGHJM24a] gave a polynomial-time 2-approximation for Prize-Collecting Steiner Forest, which the paper uses as a black box called 2APX.
--
--   There is one polynomial-time computable function $M$ on binary strings such that for every instance $J$ with nonnegative rational costs and penalties, $M$ maps the code of $J$ to the code of an edge set $F$ that is a forest of $J$ and satisfies
--   $$\mathrm{cost}(F)\le 2\,\mathrm{cost}(F')\qquad\text{for every forest }F'\text{ of }J,$$
--   equivalently $\mathrm{cost}(F)\le 2\,\mathrm{OPT}$.
--
--   This is the cited result the paper's Algorithm 1 (via Lemma 4), the bifactor algorithm and the LP-pruning procedure call.
--
--   Differences from the source:
--   - generalization: an undirected graph G = (V, E) and a set D of pairs {s_i, t_i} → an edge list on the vertex set Fin n (parallel edges and loops allowed) and a pair list (repeated pairs and s_i = t_i allowed); reason: covers more instances: a simple graph with a set of distinct pairs is the case of lists without loops, parallel edges or repeats; a loop never lies in a forest and a pair with s_i = t_i is always connected
--   - encoding: a polynomial-time algorithm on (G, c, D, π) → one function M on binary strings with PolyTimeComputable M (published QAlgorithms_ClassicalStringComputability: Mathlib multi-stack Turing machine, time polynomial in the input length), fixed before the instance, mapping the binary code encInst J of every instance J with nonnegative rational costs and penalties to the characteristic vector encEdgeSet of its output edge set; reason: bit model; Appendix B (p. 47) assumes rational input data; the vertex count n is coded in unary (the input graph G = (V, E) lists its vertices) and every other number in binary, so the time bound is polynomial in |V| plus the bit length of the data; strings that code no instance are unconstrained
--   - encoding: a solution → an edge set F that is a forest of the instance (IsForest: no loop, no edge joining two vertices already connected by the other edges of F); reason: p. 1: a feasible solution is any forest F ⊆ E
--   - reading: a polynomial-time 2-approximation → a deterministic algorithm (one function M); reason: the paper uses 2APX as a deterministic black box (it is run inside the deterministic algorithm of Theorem 1); the deterministic reading is the stronger one
-- source:
--   Bosch-Calvo, Grandoni, Mátravölgyi, Breaching the 2-Approximation Barrier for Prize-Collecting Steiner Forest, STOC 2027 submission (manuscript sha256 05d9cc28…3eb3), p. 4, §1.3 (2APX [AGHJM24a], cited; also p. 2)

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_PCSFBreach_Main_Instance
import Definitions.Def_PCSFBreach_Main_Encoding
open QAlgorithms.Complexity

namespace PCSFBreach.Main

/-- The 2-approximation 2APX of Ahmadi, Gholami, Hajiaghayi, Jabbarzade, Mahdavi [AGHJM24a],
used as a black box (p. 4). -/
theorem two_apx :
    ∃ M : Str → Str, PolyTimeComputable M ∧
      ∀ J : RatInstance, ∃ F : Finset J.toInstance.Edge,
        M (encInst J) = encEdgeSet J.toInstance F ∧ J.toInstance.IsForest F ∧
          ∀ F' : Finset J.toInstance.Edge, J.toInstance.IsForest F' → J.toInstance.cost F ≤ 2 * J.toInstance.cost F' := by sorry

end PCSFBreach.Main
