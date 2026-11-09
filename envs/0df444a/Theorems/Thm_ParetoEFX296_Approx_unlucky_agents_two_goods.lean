-- Prove2me | Theorems.Thm_ParetoEFX296_Approx_unlucky_agents_two_goods
-- name    : ParetoEFX296.Approx.unlucky_agents_two_goods
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:24:48.667011+00:00
-- url     : https://prove2.me/theorems/e32908d9-2913-45d5-9a1a-75bd7de7cc45
-- title:
--   Proof of Theorem 2, Step 1 — each unlucky agent receives at least two goods
-- statement:
--   For the table instance with integer $K\ge6$, let $\alpha>2/3+1/K$ and let $A$ be any complete $\alpha$-EFX allocation. For every agent $i$ owning neither large good,
--   $$x,y\notin A_i\quad\Longrightarrow\quad |A_i|\ge2.$$
--   This cardinality statement supplies the bundle-size restriction on unlucky agents.
--
--   Differences from the source:
--   - encoding: partitions of nine goods among agents 1,2,3,4 with integer K ≥ 6 → owner maps Good → Agent with named constructors, K : ℕ ≥ 6, and real table sums; reason: bijection with all complete integral allocations and all source integers K ≥ 6; real casts preserve every utility
--   - generalization: Definition 1 restricts α to (0,1] → the same distinct-agent EFX inequality is used for every real α above 2/3 + 1/K; reason: it agrees on the source range; for α > 1 positivity implies 1-EFX, and 1 > 2/3 + 1/K for K ≥ 6
-- source:
--   Sepideh Mahabadi, Prasanna Ramakrishnan, Jakub Tarnawski, Pareto Inefficiency of EFX, STOC 2027 submission #296 (October 2026), source.pdf SHA-256 5f34a4a4b942d95889f3403900ad796cd81a27e83d783e5ab04012fab5385ee1, p.10, Proof of Theorem 2, end of Step 1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/296.pdf

import Mathlib
import Definitions.Def_ParetoEFX296_Approx_Instance

namespace ParetoEFX296.Approx

theorem unlucky_agents_two_goods (K : ℕ) (hK : 6 ≤ K) (α : ℝ) (hα : (2 : ℝ) / 3 + 1 / (K : ℝ) < α)
    (A : Allocation Agent Good) (hEFX : IsAlphaEFX (inst K) α A) :
    ∀ i : Agent, A .x ≠ i → A .y ≠ i → 2 ≤ (bundle A i).card := by sorry

end ParetoEFX296.Approx
