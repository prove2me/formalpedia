-- Prove2me | Theorems.Thm_PooledTestingAdaptivity_Gap_Supplement_theorem_3_8
-- name    : PooledTestingAdaptivity.Gap.Supplement.theorem_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T08:39:19.468743+00:00
-- url     : https://prove2.me/theorems/1312a973-3d44-4b0c-958e-2a9ad54856f1
-- title:
--   Theorem 3.8 — DynamicGreedy attains $1/(e+1)$ of static and $1/(2(e+1))$ of dynamic optimal welfare
-- statement:
--   Let $J$ be a standard-model instance with pool cap $G$ and let $B$ be a test budget. Let $\pi$ be any DynamicGreedy policy for $(J,B)$: a policy feasible for $\mathcal F_{B,G}$ that, after every positive-probability history $H$ with remaining budget, tests a set maximizing the exact conditional gain $g(t\mid H)$ over all sets of at most $G$ individuals, stopping when the maximum gain is zero; ties are broken arbitrarily. Then
--   $$W(\pi)\ \ge\ \frac{1}{e+1}\,\mathrm{OPT}_{\mathrm{stat}}(B,J)\ \ge\ \frac{1}{2(e+1)}\,\mathrm{OPT}_{\mathrm{dyn}}(B,J).$$
--
--   Conditional greedy selection is thus a constant-factor approximation to both benchmarks, with constants $e+1$ and $2(e+1)$, $e=\exp(1)$. No positivity of either optimum is assumed.
--
--   Differences from the source:
--   - generalization: the DynamicGreedy policy (choices at reachable histories) → every feasible tree that follows the greedy rule at every positive-probability node, with arbitrary tie-breaking and arbitrary feasible choices at zero-probability nodes; reason: nodes of probability zero do not change welfare, and every DynamicGreedy policy of the source is such a tree
--   - encoding: e → Real.exp 1; reason: the same constant
-- source:
--   Edwin Lock, Nicholas Lopez, Francisco Marmolejo-Cossío, Jose Roberto Tello Ayala, David Parkes, STOC 2027 submission #1397 (October 2026), Theorem 3.8, printed p. 10, PDF p. 11; proof §6.3, printed pp. 21–22, PDF pp. 22–23

import Mathlib
import Definitions.Def_PooledTestingAdaptivity_Gap_Supplement_Greedy

namespace PooledTestingAdaptivity.Gap.Supplement

/-- Theorem 3.8 (DynamicGreedy), printed p. 10, PDF p. 11; proof §6.3, printed pp. 21–22.
Every DynamicGreedy policy, whatever its tie-breaking:
`W(π) ≥ OPT_stat(B,J)/(e+1) ≥ OPT_dyn(B,J)/(2(e+1))`. -/
theorem theorem_3_8 {n : ℕ} (J : Instance n) (B : ℕ) (π : Policy n)
    (hπ : DynamicGreedy J B π) :
    optStatic (standardFamily J B) / (Real.exp 1 + 1) ≤ dynamicWelfare J π ∧
      optDynamic (standardFamily J B) / (2 * (Real.exp 1 + 1)) ≤
        optStatic (standardFamily J B) / (Real.exp 1 + 1) := by sorry

end PooledTestingAdaptivity.Gap.Supplement
