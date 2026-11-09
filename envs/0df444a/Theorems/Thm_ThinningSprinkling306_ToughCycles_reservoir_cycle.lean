-- Prove2me | Theorems.Thm_ThinningSprinkling306_ToughCycles_reservoir_cycle
-- name    : ThinningSprinkling306.ToughCycles.reservoir_cycle
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:28:08.030817+00:00
-- url     : https://prove2.me/theorems/a2786293-9c06-43cc-bf7d-d9824d6cd2bc
-- title:
--   Lemma 5.3 (corrected: V0 nonempty) — a cycle containing the initial forest
-- statement:
--   Let $G$ be a $t$-tough finite simple graph on $n$ vertices, where $0<t\le1$. Let the integer $k\ge2$ satisfy
--   $$
--   (1-t/4)^{k-1}n<2.
--   $$
--   Let $V_0,\ldots,V_k$ be pairwise disjoint vertex sets with $V_0\ne\varnothing$, and let $F$ be a spanning linear forest of $G[V_0]$. Suppose each $G[V_i]$, $1\le i\le k$, is $t$-tough and admits a graph matching from the full endpoint set of $F$ into $V_i$ covering every endpoint. Then
--   $$
--   \text{$G$ contains a simple cycle containing every vertex of $V_0$}.
--   $$
--   Singleton components contribute their vertex to the endpoint set; in particular $|V_0|=1$ remains covered. The geometric index condition covers the source's logarithmic index with either floor or ceiling rounding. The cycle may also use vertices outside $V_0$. This is the deterministic reservoir target of Section 5.
--
--   Differences from the source:
--   - encoding: arbitrary finite simple undirected graphs → SimpleGraph (Fin n), for arbitrary natural n; reason: every finite graph admits this relabeling, including empty and singleton graphs
--   - correction: V0 may be empty → V0 is nonempty, with the singleton case retained; reason: for any M≥2, take n=2^M, t=4(1−2^(−1/8)), G=P_n and every Vi and F empty; all printed assumptions hold with exactly integral k=8M+1, but a path graph has no cycle
--   - generalization: k=log base (1−t/4) of (1/n)+1, with integer rounding suppressed → every integer k≥2 satisfying (1−t/4)^(k−1)n<2; reason: for x=log(1/n)/log(1−t/4), both k=floor(x)+1 and k=ceil(x)+1 satisfy the geometric condition since 1−t/4≥3/4; k≥2 holds for n≥2 and the n=1 source hypotheses with nonempty V0 are impossible
-- source:
--   Micha Christoph, Zach Hunter, Benny Sudakov, STOC 2027 submission #306 (October 2026), p. 11, Lemma 5.3 (PDF p. 13); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/306.pdf

import Definitions.Def_ThinningSprinkling306_ToughCycles_Paths

namespace ThinningSprinkling306.ToughCycles

/-- Lemma 5.3, printed p. 11 (PDF p. 13).
Corrected: V₀ is nonempty (all empty parts in a path graph contradict the printed statement).
The geometric stopping criterion covers the paper's floor and ceiling readings of k. -/
theorem reservoir_cycle {n k : ℕ} (G : SimpleGraph (Fin n)) (t : ℝ)
    (ht : 0 < t) (ht1 : t ≤ 1) (hG : Tough G t) (hk : 2 ≤ k)
    (hstop : (1 - t / 4) ^ (k - 1) * (n : ℝ) < 2)
    (V : Fin (k + 1) → Finset (Fin n))
    (hV : ∀ i j, i ≠ j → Disjoint (V i) (V j))
    (hV0 : (V 0).Nonempty) (F : LinearForest G (V 0))
    (hreservoirs : ∀ i : Fin (k + 1), i ≠ 0 → ToughOn G (V i) t)
    (hmatch : ∀ i : Fin (k + 1), i ≠ 0 → MatchingInto G F.endpoints (V i)) :
    CycleContaining G (V 0) := by sorry

end ThinningSprinkling306.ToughCycles
