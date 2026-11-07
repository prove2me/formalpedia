-- Prove2me | Theorems.Thm_RGMISFast_observation_2_2
-- name    : RGMISFast.observation_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:29:44.044688+00:00
-- url     : https://prove2.me/theorems/9486428a-9f49-4173-8cb5-181e11c3dc33
-- title:
--   Observation 2.2: the fresh calls of RGMIS form an admissible query tree with $Q(u^*)$ vertices
-- statement:
--   Let $G$ be a finite simple graph with distinct ranks $r:V\to[0,\infty)$ and root $u^*$, and run Procedure 1.1 from $u^*$ with an empty memo table. Then:
--
--   0. every answer recorded in the memo table, and the answer returned for $u^*$, is correct: it says whether the vertex lies in the greedy independent set $I$;
--   1. (a) ranks strictly decrease along the stack of pending calls: every call made during the scan of $v$ goes to a neighbour $w\in N(v)$ with $r(w)<r(v)$;
--   2. (b) each vertex is freshly called at most once, and the fresh calls form a tree rooted at $u^*$ with $Q(u^*)$ distinct vertices, the parent of a fresh call being the vertex whose scan made it;
--   3. (c) if $w$ is a child of $v$ in this tree, then $w\in N(v)$ and $r(w)\le\tau(v)$.
--
--   In particular the query tree is an admissible tree with $Q(u^*)$ vertices, which reduces the goal theorem to bounding admissible trees.
--
--   **Formalization Note** The calls are the events of the trace of the run: the first event is the initial call at $u^*$ and every later event has a caller. Clause (b)–(c) asserts an admissible tree whose nodes are exactly the freshly called vertices and whose parent map sends each fresh callee to its caller.
--
--   Differences from the source:
--   - encoding: distinct ranks r : V → [0, ∞), the paper's standing assumption (§1.1, p.2; §2, p.10) → hypotheses `Function.Injective r` and `∀ v, 0 ≤ r v`; reason: the standing assumption written as hypotheses; it holds almost surely
--   - encoding: the stack of pending calls and the query tree of the execution → the call trace of `run` (caller, callee, fresh), the stack being the chain of callers; reason: the execution is an explicit recursion; the trace records exactly its invocations
--   - generalization: properties (a)–(c) → (a)–(c) plus the correctness of all recorded and returned answers (App. B) and the shape of the trace (initial call first); reason: the added clauses are proved in App. B; dropping them gives the printed observation
-- source:
--   Dalirrooyfard, Makarychev, Mitrović, Ramachandran, Randomized Greedy MIS Is Fast at Every Node, STOC 2027 submission (manuscript sha256 e93cdfecc03618969d5f2ecf8171c6f84c528edcc473b2f864299e555f823664), Observation 2.2, p.11 (PDF p.13); Definition 2.3, p.11; proof and "All recorded answers are correct", App. B, p.30 (PDF p.32)

import Mathlib
import Definitions.Def_RGMISFast_AdmissibleTree

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RGMISFast

/-- Observation 2.2 with Definition 2.3 and the correctness of the recorded answers (Dalirrooyfard, Makarychev, Mitrović, Ramachandran, *Randomized Greedy MIS Is Fast at Every Node*,
STOC 2027 submission (manuscript sha256 e93cdfec…),
Observation 2.2, p.11; proof in App. B, p.30): the execution of `RGMIS(u∗)` satisfies
(0) all recorded answers are correct, (a) ranks strictly decrease along the stack of pending
calls, (b) each vertex is freshly called at most once, and the fresh calls form a tree rooted at
`u∗` with `Q(u∗)` distinct vertices, (c) if `w` is a child of `v` in this tree, then `w ∈ N(v)`
and `r(w) ≤ τ(v)`; that is, the query tree is admissible.

**Formalization Note** Ranks are distinct and nonnegative (the paper's standing assumption,
§1.1 and §2). The calls are read off the trace of `run`: each event records its caller (the
vertex whose scan made it; `none` only for the initial call), its callee, and whether it was
fresh. The stack of pending calls is the chain of callers, so (a) is the statement that every
call goes from a vertex to a neighbour of smaller rank. The fresh calls form the admissible tree
`T` whose nodes are the freshly called vertices and whose parent map sends each fresh callee to
its caller. -/
theorem observation_2_2 {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (u : V) (r : V → ℝ) (hinj : Function.Injective r)
    (hnn : ∀ v, 0 ≤ r v) :
    (∀ v b, (run G r u).2.memo v = some b → b = inMIS G r v) ∧
    (run G r u).1 = inMIS G r u ∧
    (run G r u).2.trace.head? = some ⟨none, u, true⟩ ∧
    (∀ e ∈ (run G r u).2.trace.tail, e.caller.isSome) ∧
    (∀ e ∈ (run G r u).2.trace, ∀ v, e.caller = some v → G.Adj v e.callee ∧ r e.callee < r v) ∧
    (((run G r u).2.trace.filter (fun e => e.fresh)).map (fun e => e.callee)).Nodup ∧
    (((run G r u).2.trace.filter (fun e => e.fresh)).map (fun e => e.callee)).length = Q G u r ∧
    ∃ T : AdmissibleTree G r u,
      T.nodes = (((run G r u).2.trace.filter (fun e => e.fresh)).map (fun e => e.callee)).toFinset ∧
      ∀ e ∈ (run G r u).2.trace, e.fresh = true → ∀ v, e.caller = some v → T.par e.callee = v := by sorry

end RGMISFast
