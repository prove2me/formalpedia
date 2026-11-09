-- Prove2me | Theorems.Thm_QueryDepthMIS_lemma_3_4
-- name    : QueryDepthMIS.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:33:50.328501+00:00
-- url     : https://prove2.me/theorems/76ab8f01-312e-4542-96a6-034ca7a5bebf
-- title:
--   Lemma 3.4 — few shortcuts: $\Pr[\text{some query path has} > h \text{ shortcuts}] \le (n+m)2^{-h/2}$
-- statement:
--   Let $G$ be a simple graph with $n \ge 2$ vertices and $m$ edges and $\pi$ a uniformly random permutation of $V$.
--
--   1. For every integer $h \ge 0$,
--   $$
--   \Pr[\text{some query path has more than } h \text{ shortcuts}] \le (n + m)\,2^{-h/2}.
--   $$
--   2. With $h = \lceil 18 \log n \rceil$ ($\log$ to base 2), with probability at least $1 - 1/n^7$ every query path has at most $h$ shortcuts.
--
--   Shortcuts are the triples on which the two-hop lemma cannot be used; this lemma shows there are only $O(\log n)$ of them on any query path.
--
--   Differences from the source:
--   - encoding: a uniformly random permutation π of V, π(i) the i-th vertex → the uniform (counting) law on orderings ω : V ≃ Fin n, π = ω⁻¹, with 1-based ranks rank ω v = ω v + 1; reason: the same law; positions keep the paper's 1-based values
--   - encoding: a simple graph G with no order on V → an additional instance [LinearOrder V]; reason: required by the reused RGMISFast.tau to break rank ties; ranks of a permutation are injective, so it never acts
--   - encoding: a sequence of positions p₁ < ⋯ < p_L → the list of vertices at those positions, whose ranks are the positions; reason: positions and vertices correspond bijectively under rank
-- source:
--   Mitrović–Sheu, Tight Query Depth of Recursive Randomized Greedy MIS, STOC 2027 submission (manuscript sha256 805e76d8…), Lemma 3.4, p.13

import Mathlib
import Definitions.Def_PunctSketch_coinProb
import Definitions.Def_QueryDepthMIS_IsQueryPath
import Definitions.Def_QueryDepthMIS_shortcutIdx
import Definitions.Def_QueryDepthMIS_rank

set_option autoImplicit false

namespace QueryDepthMIS

/-- Lemma 3.4 (Few shortcuts) (Mitrović–Sheu, *Tight Query Depth of Recursive Randomized Greedy MIS*, STOC 2027 submission (manuscript sha256 805e76d8…), Lemma 3.4, p.13): "For every integer h ≥ 0, Pr[some query
path has more than h shortcuts] ≤ (n + m)2^{−h/2}. In particular, set h = ⌈18 log n⌉. With
probability at least 1 − 1/n⁷, every query path has at most h shortcuts."

**Formalization Note** The number of shortcuts of a query path `l` is
`(shortcutIdx G l).card`; `m = G.edgeFinset.card`; `log` is `Real.logb 2`; `2^{−h/2}` is a real
power. `n ≥ 2` is the standing assumption of §2.1. -/
theorem lemma_3_4 :
    ∀ (V : Type) [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj],
      2 ≤ Fintype.card V →
      (∀ h : ℕ,
        PunctSketch.coinProb (fun ω : Perm V => ∃ l : List V, IsQueryPath G (rank ω) l ∧
            h < (shortcutIdx G l).card) ≤
          ((Fintype.card V : ℝ) + (G.edgeFinset.card : ℝ)) * (2 : ℝ) ^ (-(h : ℝ) / 2)) ∧
      1 - 1 / (Fintype.card V : ℝ) ^ 7 ≤
        PunctSketch.coinProb (fun ω : Perm V => ∀ l : List V, IsQueryPath G (rank ω) l →
          (shortcutIdx G l).card ≤ ⌈18 * Real.logb 2 (Fintype.card V : ℝ)⌉₊) := by sorry

end QueryDepthMIS
