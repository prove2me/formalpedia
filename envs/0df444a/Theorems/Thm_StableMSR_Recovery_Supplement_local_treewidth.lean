-- Prove2me | Theorems.Thm_StableMSR_Recovery_Supplement_local_treewidth
-- name    : StableMSR.Recovery.Supplement.local_treewidth
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T03:13:02.752235+00:00
-- url     : https://prove2.me/theorems/64d3e833-30f8-4db2-9a46-8bcd3ae19f09
-- title:
--   Lemma 4.4 — local interaction treewidth
-- statement:
--   Let $\mathcal O$ be the stable optimum of a finite metric instance with $1\le k<n$ and $1<\gamma<2$. Put $\varepsilon=\gamma-1$, $R=\max_{C\in\mathcal O}r(C)$, and $\rho=\varepsilon M/4$, where $M$ is the sum of the large-cluster radii. For every aligned region $W$ with $\operatorname{diam}(W)\le\rho$, its prescribed greedy-net interaction graph satisfies
--
--   $$\operatorname{tw}(H_W)\le\omega_\varepsilon,\qquad
--   \omega_\varepsilon\le C\varepsilon^{-4}\quad(0<\varepsilon<1),$$
--
--   for one absolute $C>0$. Here $c_\varepsilon=1+80/\varepsilon+80/\varepsilon^2$ and $\omega_\varepsilon=\lceil49c_\varepsilon^2+30c_\varepsilon\rceil$ are the published parameters. This provides the local treewidth bound for randomized recovery.
--
--   Differences from the source:
--   - encoding: Finite ordered metric input and unordered exact-k partitions → Fin n points, real metric arrays, and finite sets of nonempty disjoint blocks; reason: Input-order relabelling preserves every source instance and partition; base published definitions are reused without extra conditions
--   - encoding: tw(H_W) at the greedy net and O(epsilon^-4) → TreewidthLE on the induced graph with vertex subtype N_W, and one positive constant before every epsilon and instance; reason: The graph has exactly the finite net vertices; a bounded-width finite decomposition is the finite-graph definition of treewidth, with no empty real infimum
-- source:
--   Shyam Ravichandran, Lev Reyzin, STOC 2027 submission #1010 (October 2026), Lemma 4.4, p. 11; PDF SHA256 8bb34b0b6d31458fe6fc0848c1fc82a6083f3e9ae672e748d24cf82d5289e53e

import Definitions.Def_StableMSR_Recovery_Supplement_Partitions
import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE

set_option autoImplicit false
open scoped Classical

namespace StableMSR.Recovery.Supplement

theorem local_treewidth :
    ∃ C : ℝ, 0 < C ∧
      (∀ ε : ℝ, 0 < ε → ε < 1 → (widthBound ε : ℝ) ≤ C / ε ^ 4) ∧
      ∀ (n k : ℕ) (d : Point n → Point n → ℝ) (γ : ℝ) (O : Partition n),
        1 ≤ k → k < n → IsMetricArray d → 1 < γ → γ < 2 → Stable d k γ O →
        ∀ W : Cluster n, Aligned O W → diameter d W ≤ densityScale d O (γ - 1) →
          RobertsonSeymour1986.GM5.TreewidthLE
            (interactionGraph d (largestRadius d O) W) (widthBound (γ - 1)) := by sorry

end StableMSR.Recovery.Supplement
