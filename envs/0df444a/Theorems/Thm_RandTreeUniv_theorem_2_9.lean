-- Prove2me | Theorems.Thm_RandTreeUniv_theorem_2_9
-- name    : RandTreeUniv.theorem_2_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:11:12.35526+00:00
-- url     : https://prove2.me/theorems/1d7a2206-767a-4714-ad96-dc649392eded
-- title:
--   Theorem 2.9 (Alon–Krivelevich–Sudakov) — almost-spanning bounded-degree trees in $G(n,C/n)$
-- statement:
--   For every $\varepsilon>0$ and every integer $\Delta\ge2$ there is $C=C(\varepsilon,\Delta)>0$ such that, with probability tending to $1$ as $n\to\infty$, the random graph $G(n,C/n)$ contains copies of **all** trees on at most $(1-\varepsilon)n$ vertices with maximum degree at most $\Delta$, simultaneously.
--
--   The theorem is cited from Alon, Krivelevich and Sudakov (2007). In the proof of Theorem 1 it embeds the forest left after removing long bare paths from a tree of $\mathcal T_1$ (§5).
--
--   Differences from the source:
--   - encoding: vertex set [n] = {1,…,n} → Fin n = {0,…,n−1}; reason: relabelling; same graphs up to isomorphism
--   - encoding: G(n,p) with p = p(n) a probability → published erProb n p, which clamps p to [0,1]; reason: the clamp is the identity on [0,1], and the edge probabilities used lie in [0,1] for all large n
--   - encoding: isomorphic copy as a subgraph → SimpleGraph.IsContained (injective edge-preserving map, not necessarily induced); reason: same notion
--   - encoding: trees on at most (1 − ε)n vertices → trees on Fin m for every m with (m : ℝ) ≤ (1 − ε)n; reason: every such tree is isomorphic to one on Fin m
-- source:
--   A. Cohen Antonir, L. Lichev, M. Zhukovskii, Universality in random graphs via optimal linking systems: trees and beyond, arXiv:2608.06358 (held revision, sha256 33e85b21…69a55921), Theorem 2.9, p.12 (PDF 13) (cited from Alon–Krivelevich–Sudakov 2007)

import Mathlib
import Definitions.Def_LPCommunity_SBMRecovery_Setting
import Definitions.Def_RandTreeUniv_InTreeFamily

set_option autoImplicit false

open scoped Classical
open LPCommunity.SBMRecovery

namespace RandTreeUniv

/-- **Theorem 2.9** (Alon–Krivelevich–Sudakov 2007; Cohen Antonir, Lichev, Zhukovskii, *Universality in random graphs via optimal linking systems: trees and beyond*, arXiv:2608.06358 (held revision, sha256 33e85b21…), p.12 (PDF 13)). For every `ε > 0` and
every integer `∆ ≥ 2`, there exists `C = C(ε, ∆) > 0` such that, with high probability, the
random graph `G(n, C/n)` contains copies of all trees on at most `(1 − ε)n` vertices and maximum
degree at most `∆`.

**Formalization Note** `G(n, p)` is the published `erProb n p` on `Fin n`; `whp` ("with probability tending to 1 as `n → ∞`", footnote 2, p.1) is
`Tendsto … atTop (𝓝 1)`. A tree on `m` vertices is a tree on `Fin m`; all trees with
`m ≤ (1 − ε)n` (real comparison) are required simultaneously, inside the probability. Copies are
`SimpleGraph.IsContained` (non-induced). -/
theorem theorem_2_9 (ε : ℝ) (hε : 0 < ε) (Δ : ℕ) (hΔ : 2 ≤ Δ) :
    ∃ C : ℝ, 0 < C ∧
      Filter.Tendsto
        (fun n : ℕ => erProb n (C / n) (fun G =>
          ∀ m : ℕ, (m : ℝ) ≤ (1 - ε) * n →
            ∀ T : SimpleGraph (Fin m), InTreeFamily Δ T → T.IsContained G))
        Filter.atTop (nhds 1) := by sorry

end RandTreeUniv
