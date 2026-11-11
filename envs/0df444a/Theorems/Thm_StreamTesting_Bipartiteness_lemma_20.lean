-- Prove2me | Theorems.Thm_StreamTesting_Bipartiteness_lemma_20
-- name    : StreamTesting.Bipartiteness.lemma_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T22:00:45.615645+00:00
-- url     : https://prove2.me/theorems/a77caba7-04ce-4960-8cce-22562161f886
-- title:
--   Lemma 20 — few lifted roots in each projected component force a forest
-- statement:
--   Let $H$ be a finite simple graph, choose either lift $G_s$, a labeling $\Lambda$, a deterministic policy $A$, and an arrival order $\sigma$. Let $k\ge2$ and $L\ge1$ be integers with $4kL<\operatorname{girth}(H)$. Suppose there is no simple path of $L$ edges increasing in arrival order. Write $B=\pi(T_\Lambda)$ for the actual projected revealed graph and $R$ for the actual lifted roots. If
--
--   $$\forall v\in V(H),\quad |\{r\in R:\pi(r)\text{ lies in the }B\text{-component of }v\}|<k,$$
--
--   then $B$ is a forest. Roots are counted as distinct lifted vertices, even when their projections coincide; all isolated vertices and components with no roots remain included. This is the deterministic implication used with the source cutoff and root-count regime.
--
--   Differences from the source:
--   - encoding: finite simple graphs on [n], with n/2 base vertices → SimpleGraph (Fin n); base graphs on Fin m and lifts on Fin m × Bool with n = 2m; reason: zero-based relabeling preserves all graphs, unordered edges, arrival permutations, and the exact normalization
--   - encoding: girth inequalities with infinite girth for forests → the same inequality required for every cycle length; reason: cycle-length predicates retain infinite forest girth and do not use the zero-valued natural girth default
--   - encoding: deterministic forward-only neighborhood-query testers → arbitrary deterministic observed-history decision tables with actual recursive execution; reason: the current label and prior observed history determine every decision; arbitrary tables preserve unrestricted memory, computation, and adaptivity
--   - generalization: the fixed H family, L = ceil(4 log n/log log n), and k = O(log log n) → every finite H, every integer L ≥ 1, and every k ≥ 2 satisfying the identical strict girth inequality; reason: the deterministic proof on p.25 uses only event E, the root count and 4kL < girth(H); the source cutoff is positive eventually and every source k is included
-- source:
--   Omri Ben-Eliezer, Krzysztof Onak, Sandeep Silwal, Yinzhan Xu, Sublinear-Time Algorithms on Massive Data Streams, STOC 2027 submission #1068 (October 2026); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1068.pdf; SHA256 ca9e204557da80369cd1ee2d960723e20f3d84c40adff5e96b84d7163e827e00; Lemma 20, printed p.25 / PDF p.25; standing model pp.3–4 and §4; proofs pp.25–26 and 40–41.

import Definitions.Def_StreamTesting_Bipartiteness_Roots
import Definitions.Def_StreamTesting_Bipartiteness_Execution
import Definitions.Def_StreamTesting_Bipartiteness_IncreasingPaths
import Definitions.Def_StreamTesting_Bipartiteness_Girth

noncomputable section

namespace StreamTesting.Bipartiteness

/-- Lemma 20, p.25: the deterministic assertion for every k and cutoff L.
An isolated B-component with no root is included by the universal vertex quantifier. -/
theorem lemma_20 {m : ℕ} (H : SimpleGraph (Fin m)) (s : Bool) (Λ : Labeling m)
    (A : Policy (2 * m)) (σ : Order (2 * m)) (k L : ℕ)
    (hk : 2 ≤ k) (hL : 1 ≤ L) (hgirth : GirthGreater H (4 * (k : ℝ) * (L : ℝ)))
    (hE : NoIncreasingPath (labeledGraph H s Λ) σ L)
    (hroots : ∀ v : Fin m,
      componentRootCount (projection Λ (execute (labeledGraph H s Λ) A σ))
        (roots Λ (execute (labeledGraph H s Λ) A σ)) v < k) :
    (projection Λ (execute (labeledGraph H s Λ) A σ)).IsAcyclic := by sorry

end StreamTesting.Bipartiteness
