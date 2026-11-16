-- Prove2me | Theorems.Thm_TreeEdgeRankPC_Supplement_theorem_4_11
-- name    : TreeEdgeRankPC.Supplement.theorem_4_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:10:17.760331+00:00
-- url     : https://prove2.me/theorems/93f72226-4340-465e-9b9b-e4f2a3b602d4
-- title:
--   Theorem 4.11 — distinguishing $\mathrm{er}(T)\le K$ from $\mathrm{er}(T)\ge K+r$ is P-complete under NC¹ many-one reductions, also for trees of diameter at most $6r$
-- statement:
--   Fix an integer $r\ge1$. Given a tree $T$ and an integer $K\ge0$, promised that either
--   $$\mathrm{er}(T)\le K\qquad\text{or}\qquad \mathrm{er}(T)\ge K+r,$$
--   deciding which inequality holds is P-complete under NC¹ many-one reductions, and the hardness remains for trees of diameter at most $6r$. Explicitly, each of the two promise problems
--
--   1. YES $=\{\langle T,K\rangle:\mathrm{er}(T)\le K\}$ against NO $=\{\langle T,K\rangle:\mathrm{er}(T)\ge K+r\}$, over all trees, and
--   2. the same pair restricted to trees of diameter at most $6r$,
--
--   is decided by some language in P, and every language $L'\in\mathrm P$ reduces to it by a logspace-uniform NC¹ map sending members of $L'$ to YES instances and non-members to NO instances.
--
--   Here $\mathrm{er}(T)$ is the edge ranking number of $T$. The theorem says that, unless NC $=$ P, no NC algorithm approximates $\mathrm{er}(T)$ within any constant additive error; it extends the gap-one hardness of Theorem 1.1.
--
--   Differences from the source:
--   - reading: "promised that either …, deciding which inequality holds is P-complete" → a promise problem (YES, NO) that is decided by some language of P containing YES and disjoint from NO, and to which every language of P reduces mapping members to YES and non-members to NO; reason: the standard meaning of P-completeness for a promise problem, with §3.2's NC¹ many-one reductions
--   - reading: "P-complete …. The hardness remains for trees of diameter at most 6r" → both halves (membership and hardness) for all trees and for trees of diameter at most 6r; reason: the restricted problem is a subproblem of one in P, so membership holds for it too, and stating both makes the restricted claim a full P-completeness as in Theorem 1.1
--   - reading: "uniform" family → logspace-uniform family; reason: p.12 defines only this uniformity; a weaker one would make the hardness claim weaker
--   - encoding: NC¹ computation of a polynomial-length string → the published `NC1Computable`, with (valid bit, data bit) output pairs, size ≤ n^k + k, depth ≤ c·⌊log₂ n⌋ + c; reason: the base mission's convention for outputs of varying length
--   - encoding: the instance (T, K) and problems in P → binary code `encTree T K`, languages over {0, 1}, P = the published `CookPvsNP.P Bool`; diameter ≤ 6r as ∀ u v, dist(u, v) ≤ 6r; reason: the base mission's conventions; the code is injective and a non-code is no instance
-- source:
--   Giliberti–Hajiaghayi–Yun, Parallel Edge Ranking of Trees, arXiv:2610.12438 (held version of 2026-11-02, sha256 9e04ca7b…), Theorem 4.11, p.21

import Mathlib
import Definitions.Def_TreeEdgeRankPC_Supplement_GapPromise

namespace TreeEdgeRankPC.Supplement

open TreeEdgeRankPC

/-- **Theorem 4.11** (Constant additive gap), §4.3, p.21, Giliberti–Hajiaghayi–Yun, *Parallel Edge
Ranking of Trees*, arXiv:2610.12438 (held version of 2026-11-02, sha256 9e04ca7b…): "Fix an integer
r ≥ 1. Given a tree T and an integer K ≥ 0, promised that either er(T) ≤ K or er(T) ≥ K + r, deciding
which inequality holds is P-complete under NC^1 many-one reductions. The hardness remains for trees
of diameter at most 6r."

**Formalization Note.** Two promise problems, each with both halves of P-completeness (membership in
`CookPvsNP.P Bool`, and a logspace-uniform NC¹ many-one reduction from every language in it, mapping
YES into YES and NO into NO): for all trees (`TER` against `GapNo r`), and for trees of diameter at
most `6r` (`GapYesDiam (6 * r)` against `GapNoDiam r (6 * r)`). `r` is fixed first; the reductions
may depend on it. `K` is in binary. -/
theorem theorem_4_11 (r : ℕ) (hr : 1 ≤ r) :
    PromisePCompleteNC1 TER (GapNo r) ∧
      PromisePCompleteNC1 (GapYesDiam (6 * r)) (GapNoDiam r (6 * r)) := by sorry

end TreeEdgeRankPC.Supplement
