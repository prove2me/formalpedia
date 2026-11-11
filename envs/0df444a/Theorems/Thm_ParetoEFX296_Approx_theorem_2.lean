-- Prove2me | Theorems.Thm_ParetoEFX296_Approx_theorem_2
-- name    : ParetoEFX296.Approx.theorem_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T10:24:55.236297+00:00
-- url     : https://prove2.me/theorems/d04ecd3c-a0bb-48d4-800b-2505db991068
-- title:
--   Theorem 2 — positive table and no Pareto optimal α-EFX allocation above 2/3 + 1/K
-- statement:
--   For each integer $K\ge6$, consider the four-agent, nine-good additive table $\mathrm{inst}(K)$ of Theorem 2. Every entry is positive, and for every real $\alpha>2/3+1/K$,
--   $$\bigl(\forall i,g,\ v_i(g)>0\bigr)\quad\text{and}\quad
--   \nexists A:\ A\text{ is }\alpha\text{-EFX and Pareto optimal}.$$
--   Allocations are all complete integral partitions of the nine goods, possibly with empty bundles, and Pareto optimality compares with every such allocation. Some agent must strictly improve in a Pareto domination. The statement preserves all values in the explicit table and the full range $K\ge6$; it is the page 9 theorem together with positivity from its page 3 formulation. Taking $K$ arbitrarily large recovers the impossibility for every $\alpha>2/3$. It asserts incompatibility with Pareto optimality, and does not assert nonexistence of EFX allocations alone.
--
--   Differences from the source:
--   - encoding: partitions of nine goods among agents 1,2,3,4 with integer K ≥ 6 → owner maps Good → Agent with named constructors, K : ℕ ≥ 6, and real table sums; reason: bijection with all complete integral allocations and all source integers K ≥ 6; real casts preserve every utility
--   - generalization: Definition 1 restricts α to (0,1] → the same distinct-agent EFX inequality is used for every real α above 2/3 + 1/K; reason: it agrees on the source range; for α > 1 positivity implies 1-EFX, and 1 > 2/3 + 1/K for K ≥ 6
-- source:
--   Sepideh Mahabadi, Prasanna Ramakrishnan, Jakub Tarnawski, Pareto Inefficiency of EFX, STOC 2027 submission #296 (October 2026), source.pdf SHA-256 5f34a4a4b942d95889f3403900ad796cd81a27e83d783e5ab04012fab5385ee1, p.9, Theorem 2; p.3, Theorem 2 positivity clause; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/296.pdf

import Mathlib
import Definitions.Def_ParetoEFX296_Approx_Instance

namespace ParetoEFX296.Approx

theorem theorem_2 (K : ℕ) (hK : 6 ≤ K) :
    (∀ (i : Agent) (g : Good), 0 < inst K i g) ∧
    ∀ α : ℝ, (2 : ℝ) / 3 + 1 / (K : ℝ) < α →
      ¬ ∃ A : Allocation Agent Good,
        IsAlphaEFX (inst K) α A ∧ IsParetoOptimal (inst K) A := by sorry

end ParetoEFX296.Approx
