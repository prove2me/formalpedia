-- Prove2me | Theorems.Thm_ParetoEFX296_Approx_Supplement_theorem_1
-- name    : ParetoEFX296.Approx.Supplement.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:31:47.386684+00:00
-- url     : https://prove2.me/theorems/73f24dfc-b9b3-42ec-8b2f-bc396a8b684e
-- title:
--   Theorem 1 — the four-agent, eight-good instance has no allocation that is both EFX and Pareto optimal
-- statement:
--   Consider the four agents $1,2,3,4$ and the eight goods $x,y,a,b,c,d,p,q$ with the additive valuations
--   $$\begin{array}{c|rrrrrrrr}&x&y&a&b&c&d&p&q\\\hline 1&7&6&3&3&1&1&2&1\\2&6&7&1&3&3&1&1&2\\3&7&6&1&1&3&3&2&1\\4&6&7&3&1&1&3&1&2\end{array}$$
--   An allocation $A=(A_1,\dots,A_4)$ is a partition of the eight goods into four (possibly empty) bundles, agent $i$ receiving $A_i$. It is **EFX** if for all agents $i\ne j$ and every good $g\in A_j$,
--   $$v_i(A_i)\ \ge\ v_i(A_j\setminus\{g\}).$$
--   An allocation $B$ **Pareto dominates** $A$ if $v_i(B_i)\ge v_i(A_i)$ for every agent $i$ with at least one strict inequality, and $A$ is **Pareto optimal** if no allocation dominates it. The theorem states that
--   $$\nexists A:\ A\text{ is EFX and Pareto optimal}.$$
--
--   The instance has positive values only, so it answers a question of Plaut and Roughgarden: Pareto optimal EFX allocations need not exist even when every agent values every good. The theorem does not claim that EFX allocations fail to exist in this instance; it asserts their incompatibility with Pareto optimality.
--
--   **Formalization Note** Allocations are owner maps from the eight goods to the four agents (the published `Allocation`), so empty bundles are allowed and every good is allocated. EFX is the published `IsAlphaEFX` at $\alpha=1$, which is the paper's Definition 1 with "EFX = 1-EFX". Pareto competitors range over all complete allocations of the same eight goods.
--
--   Differences from the source:
--   - encoding: partitions of the eight goods among agents 1, 2, 3, 4 with integer values → owner maps Good8 → Agent with named constructors and real-valued additive sums; reason: owner maps are in bijection with complete integral allocations, and real casts preserve every utility and comparison
-- source:
--   Sepideh Mahabadi, Prasanna Ramakrishnan, Jakub Tarnawski, Pareto Inefficiency of EFX, STOC 2027 submission #296 (October 2026), source.pdf SHA-256 5f34a4a4b942d95889f3403900ad796cd81a27e83d783e5ab04012fab5385ee1, p.3, Theorem 1; Definitions 1–2, p.5; proof pp.7–8; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/296.pdf

import Mathlib
import Definitions.Def_ParetoEFX296_Approx_Supplement_Table1

namespace ParetoEFX296.Approx.Supplement

open ParetoEFX296.Approx

theorem theorem_1 :
    ¬ ∃ A : Allocation Agent Good8,
      IsAlphaEFX v1 1 A ∧ IsParetoOptimal v1 A := by sorry

end ParetoEFX296.Approx.Supplement
