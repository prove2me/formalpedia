-- Prove2me | Theorems.Thm_PCSFBreach_Main_theorem_1
-- name    : PCSFBreach.Main.theorem_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:57:05.622382+00:00
-- url     : https://prove2.me/theorems/89532eae-b1ed-4b78-ad55-84c8ef9f9cbb
-- title:
--   Theorem 1 — a polynomial-time (2 − δ)-approximation for Prize-Collecting Steiner Forest with δ > 10⁻²⁵
-- statement:
--   There are a real number $\delta>10^{-25}$ and one polynomial-time computable function $M$ on binary strings such that for every Prize-Collecting Steiner Forest instance $J$ — a graph on vertices $\{0,\dots,n-1\}$ given by an edge list with nonnegative rational costs, and a list of demand pairs with nonnegative rational penalties — $M$ maps the binary code of $J$ to the code of an edge set $F$ that is a forest of $J$ and satisfies
--   $$\mathrm{cost}(F)=c(F)+\pi(\bar D(F))\le(2-\delta)\cdot\mathrm{OPT}(J),$$
--   where $\mathrm{OPT}(J)$ is the minimum of $\mathrm{cost}$ over all forests of $J$.
--
--   This is the first approximation ratio below 2 for PCSF, improving the factor-2 algorithm of Ahmadi et al. [AGHJM24a].
--
--   Differences from the source:
--   - generalization: an undirected graph G = (V, E) and a set D of pairs {s_i, t_i} → an edge list on the vertex set Fin n (parallel edges and loops allowed) and a pair list (repeated pairs and s_i = t_i allowed); reason: covers more instances: a simple graph with a set of distinct pairs is the case of lists without loops, parallel edges or repeats; a loop never lies in a forest and a pair with s_i = t_i is always connected
--   - encoding: a polynomial-time algorithm on (G, c, D, π) → one function M on binary strings with PolyTimeComputable M (published QAlgorithms_ClassicalStringComputability: Mathlib multi-stack Turing machine, time polynomial in the input length), fixed before the instance, mapping the binary code encInst J of every instance J with nonnegative rational costs and penalties to the characteristic vector encEdgeSet of its output edge set; reason: bit model; Appendix B (p. 47) assumes rational input data; the vertex count n is coded in unary (the input graph G = (V, E) lists its vertices) and every other number in binary, so the time bound is polynomial in |V| plus the bit length of the data; strings that code no instance are unconstrained
--   - encoding: a solution → an edge set F that is a forest of the instance (IsForest: no loop, no edge joining two vertices already connected by the other edges of F); reason: p. 1: a feasible solution is any forest F ⊆ E
--   - reading: a polynomial-time 2 − δ approximation → one deterministic PolyTimeComputable function M fixed before the instance; reason: the paper derandomizes its only randomized step (Remark 1) and contrasts deterministic and randomized ratios (p. 2); the deterministic reading is the stronger one
-- source:
--   Bosch-Calvo, Grandoni, Mátravölgyi, Breaching the 2-Approximation Barrier for Prize-Collecting Steiner Forest, STOC 2027 submission (manuscript sha256 05d9cc28…3eb3), p. 2, Theorem 1 (restated as Theorem 4, p. 46; proof in Appendix A, pp. 46–47)

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_PCSFBreach_Main_Instance
import Definitions.Def_PCSFBreach_Main_Encoding
open QAlgorithms.Complexity

namespace PCSFBreach.Main

/-- Theorem 1 (p. 2): there is a polynomial-time `2 − δ` approximation for PCSF for an absolute
constant `δ > 10⁻²⁵`. -/
theorem theorem_1 :
    ∃ δ : ℝ, (1 : ℝ) / 10 ^ 25 < δ ∧
      ∃ M : Str → Str, PolyTimeComputable M ∧
        ∀ J : RatInstance, ∃ F : Finset J.toInstance.Edge,
          M (encInst J) = encEdgeSet J.toInstance F ∧ J.toInstance.IsForest F ∧
            J.toInstance.cost F ≤ (2 - δ) * J.toInstance.OPT := by sorry

end PCSFBreach.Main
