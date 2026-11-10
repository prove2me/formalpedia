-- Prove2me | Theorems.Thm_RandTreeUniv_theorem_1_tree_universality
-- name    : RandTreeUniv.theorem_1_tree_universality
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:11:10.824206+00:00
-- url     : https://prove2.me/theorems/359a25ef-dbc3-4478-bcbd-944093924949
-- title:
--   Theorem 1 — one absolute $C$ makes $G(n,C\ln n/n)$ whp $\mathcal T_{n,\Delta}$-universal for every fixed $\Delta$
-- statement:
--   There exists a constant $C>1$ such that, for every constant $\Delta\ge2$,
--
--   $$
--   \lim_{n\to\infty}\mathbb P\Big(G\big(n,C\ln n/n\big)\ \text{contains a copy of every tree on } n \text{ vertices with maximum degree at most }\Delta\Big)=1 .
--   $$
--
--   Here $G(n,p)$ is the binomial random graph on $[n]$ in which each pair is an edge independently with probability $p$, and "a copy" means a (not necessarily induced) subgraph isomorphic to the tree. The constant $C$ does not depend on $\Delta$; the speed of convergence may. All trees must be present in the same random graph.
--
--   This answers Montgomery's question whether the threshold for $\mathcal T_{n,\Delta}$-universality is at most $C\ln n/n$ with $C$ independent of $\Delta$; up to the value of $C$ the edge probability is optimal, since below $\ln n/n$ the random graph has isolated vertices.
--
--   Differences from the source:
--   - encoding: vertex set [n] = {1,…,n} → Fin n = {0,…,n−1}; reason: relabelling; same graphs up to isomorphism
--   - encoding: G(n,p) with p = p(n) a probability → published erProb n p, which clamps p to [0,1]; reason: the clamp is the identity on [0,1], and the edge probabilities used lie in [0,1] for all large n
--   - encoding: isomorphic copy as a subgraph → SimpleGraph.IsContained (injective edge-preserving map, not necessarily induced); reason: same notion
-- source:
--   A. Cohen Antonir, L. Lichev, M. Zhukovskii, Universality in random graphs via optimal linking systems: trees and beyond, arXiv:2608.06358 (held revision, sha256 33e85b21…69a55921), Theorem 1, p.4 (PDF 5)

import Mathlib
import Definitions.Def_LPCommunity_SBMRecovery_Setting
import Definitions.Def_RandTreeUniv_InTreeFamily
import Definitions.Def_RandTreeUniv_IsUniversal

set_option autoImplicit false

open scoped Classical
open LPCommunity.SBMRecovery

namespace RandTreeUniv

/-- **Theorem 1** (Cohen Antonir, Lichev, Zhukovskii, *Universality in random graphs via optimal linking systems: trees and beyond*, arXiv:2608.06358 (held revision, sha256 33e85b21…), p.4 (PDF 5)). There exists a constant `C > 1` such that, for every
constant `∆ ≥ 2`, whp `G(n, C ln n/n)` is `T_{n,∆}`-universal: with probability tending to `1`
as `n → ∞`, the binomial random graph on `[n]` with edge probability `C ln n/n` contains a copy
of every tree on `n` vertices with maximum degree at most `∆`, all at once.

**Formalization Note** `G(n, p)` is the published law `erProb n p` on graphs on `Fin n`
(independent edges with probability `p` clamped to `[0, 1]`; `C ln n/n ∈ [0, 1]` for all large
`n`). The constant `C` is chosen before `∆`; the rate of convergence may depend on `∆`. The
quantifier over trees is inside the probability. Copies are `SimpleGraph.IsContained`
(non-induced). `ln` is `Real.log`. -/
theorem theorem_1_tree_universality :
    ∃ C : ℝ, 1 < C ∧ ∀ Δ : ℕ, 2 ≤ Δ →
      Filter.Tendsto
        (fun n : ℕ => erProb n (C * Real.log n / n) (fun G => IsUniversal G (InTreeFamily Δ)))
        Filter.atTop (nhds 1) := by sorry

end RandTreeUniv
