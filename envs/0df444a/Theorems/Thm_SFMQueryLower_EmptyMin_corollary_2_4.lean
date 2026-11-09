-- Prove2me | Theorems.Thm_SFMQueryLower_EmptyMin_corollary_2_4
-- name    : SFMQueryLower.EmptyMin.corollary_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:23:59.97346+00:00
-- url     : https://prove2.me/theorems/9443d3cd-8101-4120-bf91-63d024f73f4b
-- title:
--   Corollary 2.4 — the distinguishing query has probability at least one third
-- statement:
--   Let $n\ge2$, fix an ordered nonempty-block partition $\Pi$, and let $P^\star=\bigcup_iP_i$. Suppose the same randomized algorithm $A$ decides whether the empty set minimizes $f_b^\Pi$ with error at most $1/3$ separately for $b=0,1$. Then
--   $$\Pr_A\{A\text{ queries }P^\star\text{ on }f_1^\Pi\}\ge\frac13.$$
--   The event refers to an actual issued query at some finite interaction time. Correctness is assumed only for these two fixed inputs. This is the probability statement needed by the stopping-layer lower bound.
--
--   **Formalization Note** The seed is independent of the fixed partition. Failure to return correctly counts as failure; infinite expected costs are allowed.
--
--   Differences from the source:
--   - encoding: finite labeled ground sets and their subsets → Fin n and Finset (Fin n); reason: bijections relabel every finite source instance
--   - encoding: layers indexed from 1 and bits in {0,1} → blocks indexed by Fin k with Boolean slots, and Bool hidden bits; reason: source index j+1 corresponds to stored index j and false/true to 0/1
--   - encoding: internal randomized oracle interaction and expected queries → an arbitrary probability seed chooses a causal history strategy; costs are nonnegative extended series; reason: includes general measurable randomness and stopping, preserves infinite cost, and requires only observable-event measurability
--   - generalization: ordinary solving algorithms return answers almost surely → nonreturning runs are also allowed and counted as failures; reason: all almost surely halting source algorithms are included; the same indistinguishability and issue-count bounds apply to unsuccessful nonreturning runs
-- source:
--   James Fox, Randomized Query Lower Bounds for Submodular Function Minimization, STOC 2027 submission #292 (October 2026), Corollary 2.4, printed p. 8 / PDF p. 9

import Definitions.Def_SFMQueryLower_EmptyMin_EmptyMinProblem
import Definitions.Def_SFMQueryLower_EmptyMin_HardFamily

set_option autoImplicit false
open scoped ENNReal

namespace SFMQueryLower.EmptyMin

/-- Fox, Corollary 2.4, printed p.8 / PDF p.9. Accuracy is required only on
the two fixed functions, not globally over all submodular inputs. -/
theorem corollary_2_4 (n k : ℕ) (hn : 2 ≤ n) (π : OrderedPartition n k)
    (A : EmptyMinAlgorithm n)
    (h0 : CorrectOn A (1 / 3) (hardFunction π false))
    (h1 : CorrectOn A (1 / 3) (hardFunction π true)) :
    (1 / 3 : ℝ≥0∞) ≤ queryProbability A (hardFunction π true) (distinguishedSet π) := by sorry

end SFMQueryLower.EmptyMin
