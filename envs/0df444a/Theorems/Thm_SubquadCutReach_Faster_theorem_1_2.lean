-- Prove2me | Theorems.Thm_SubquadCutReach_Faster_theorem_1_2
-- name    : SubquadCutReach.Faster.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T17:04:00.516813+00:00
-- url     : https://prove2.me/theorems/894b6490-fd61-450a-abfa-f9a9abf17f1e
-- title:
--   Theorem 1.2 — Faster protocol
-- statement:
--   There is one uniform randomized zero-error outgoing-cut-oracle program deciding directed $s$–$t$ reachability on every finite labelled oriented graph. Put $L(n)=\log(n+2)$ and let $Q$ be its stopping query count. Positive constants and fixed logarithmic powers, independent of graph, size and terminals, satisfy
--
--   $$\mathbb E Q\le C_En^{5/3}L(n)^{p_E}.$$
--
--   For each fixed $c>0$, constants $C_c>0,p_c$ and threshold $N_c$, also independent of the input, satisfy $\Pr\{Q>C_cn^{5/3}L(n)^{p_c}\}\le n^{-c}$ for all $n\ge N_c$. The program is the same across all these bounds. Every returning execution gives the correct bit, and termination is almost sure. Nontermination has infinite cost. All oriented graphs and all terminals, including $s=t$, are included. This is the full faster headline, with both cost modes and no direct graph access.
--
--   Differences from the source:
--   - encoding: finite labelled oracle inputs and O or Õ bounds → Fin n, finite rational-literal oracle programs, charged queries and outer uniform positive constants; reason: relabeling and an operational cost semantics preserve the source input domain; nontermination has infinite cost
-- source:
--   Henry Fleischmann, Sagnik Mukhopadhyay, Swagato Sanyal, STOC 2027 submission #503 (October 2026), p. 2, Theorem 1.2 (PDF p. 4)

import Definitions.Def_SubquadCutReach_Faster_Tasks

set_option autoImplicit false

namespace SubquadCutReach.Faster

/-- Theorem 1.2, p.2 (PDF 4). One finite program, independent of size, graph and terminals.
Both cost modes concern the same zero-error algorithm. -/
theorem theorem_1_2 :
    ∃ P : Program, Admissible P ∧ (∀ i : ReachCase, ReachCorrect P i) ∧
      SoftBounds ReachCase ReachCase.n (reachCosts P) (fun i => scale i.n) := by sorry

end SubquadCutReach.Faster
