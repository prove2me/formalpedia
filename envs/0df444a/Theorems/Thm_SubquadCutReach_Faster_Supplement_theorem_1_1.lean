-- Prove2me | Theorems.Thm_SubquadCutReach_Faster_Supplement_theorem_1_1
-- name    : SubquadCutReach.Faster.Supplement.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:25:57.206832+00:00
-- url     : https://prove2.me/theorems/a250f87c-dec9-4946-954d-1938b8eceb09
-- title:
--   Theorem 1.1 — Warm-up protocol ($\tilde O(n^{9/5})$ queries)
-- statement:
--   There is one uniform randomized zero-error outgoing-cut-oracle program deciding directed $s$–$t$ reachability on every finite labelled oriented graph $G$ (no loops, no 2-cycles), with arbitrary terminals $s,t$, including $s=t$. Put $L(n)=\log(n+2)$ and let $Q$ be its stopping query count. Positive constants and a fixed logarithmic power, independent of graph, size and terminals, satisfy
--
--   $$\mathbb E\,Q\le C_E\,n^{9/5}L(n)^{p_E}.$$
--
--   For each fixed $c>0$, constants $C_c>0$, $p_c$ and a threshold $N_c$, also independent of the input, satisfy $\Pr\{Q>C_c\,n^{9/5}L(n)^{p_c}\}\le n^{-c}$ for all $n\ge N_c$. Every returning execution outputs the correct bit, termination is almost sure, and nontermination has infinite cost. The same program meets both cost bounds, and the graph is accessible only through outgoing-cut queries $S\mapsto|\{(u,v)\in E(G):u\in S,v\notin S\}|$.
--
--   This is the warm-up headline of the paper: already subquadratic, through a shorter route than the mission's goal (Theorem 1.2, exponent $5/3$), which it is logically implied by. It is posed on its own and not derived from the goal.
--
--   Differences from the source:
--   - encoding: finite labelled oracle inputs and $\tilde O$ bounds in expectation and with high probability → `Fin n`, finite rational-literal oracle programs, charged queries and the published `SoftBounds` with outer uniform positive constants; reason: relabeling and the mission's operational cost semantics preserve the source input domain; nontermination has infinite cost
-- source:
--   Henry Fleischmann, Sagnik Mukhopadhyay, Swagato Sanyal, STOC 2027 submission #503 (October 2026), p. 2, Theorem 1.1 (PDF p. 4); analysis §3.2.1, §3.4, §4 (pp. 8–16, PDF pp. 10–18)

import Definitions.Def_SubquadCutReach_Faster_Tasks
import Definitions.Def_SubquadCutReach_Faster_Supplement_Warmup

set_option autoImplicit false

namespace SubquadCutReach.Faster.Supplement

open SubquadCutReach.Faster

/-- Theorem 1.1, p. 2 (PDF 4). One finite program, independent of size, graph and terminals;
zero error, both cost modes, query scale `n^(9/5)` up to polylogarithmic factors. -/
theorem theorem_1_1 :
    ∃ P : Program, Admissible P ∧ (∀ i : ReachCase, ReachCorrect P i) ∧
      SoftBounds ReachCase ReachCase.n (reachCosts P) (fun i => warmScale i.n) := by sorry

end SubquadCutReach.Faster.Supplement
