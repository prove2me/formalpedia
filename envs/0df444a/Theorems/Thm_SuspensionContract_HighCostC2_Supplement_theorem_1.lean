-- Prove2me | Theorems.Thm_SuspensionContract_HighCostC2_Supplement_theorem_1
-- name    : SuspensionContract.HighCostC2.Supplement.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T21:06:28.629976+00:00
-- url     : https://prove2.me/theorems/15d2ede4-8b56-47e4-bc34-13e04f94b03d
-- title:
--   Theorem 1 (corrected: deterministic controls and supremum convention)
-- statement:
--   Let $V_I,V_\emptyset$ be continuous, concave, nondecreasing functions on $\mathbb R_+$ satisfying all of (20)–(22). For every feasible contract $\Gamma$ whose complying agent utility is $w\ge0$,
--   $$U(\Gamma)\le V_\emptyset(w)-w.$$
--   Consequently the extended optimum satisfies
--   $$\mathcal Z\le\sup_{w\ge0}\{V_\emptyset(w)-w\}.$$
--   The pointwise conclusion and the global upper envelope are both retained. Principal utility can be $-\infty$, and the upper envelope can be $+\infty$; no unattested maximizer, differentiability at a kink, or finite derivative at zero is assumed.
--
--   Differences from the source:
--   - correction: D is called deterministic but only F-adaptedness is written. → The public filtration after initialization contains no noise beyond N and Q.; reason: Adaptedness alone admits an independent Poisson D and falsifies the two-noise PK equation; this implements the intended deterministic control. See DISPROOF.md.
--   - reading: (20) is printed at w≥0 with a left-derivative convention. → The published OptCond uses (20) at w>0 and retains (21),(22) at zero.; reason: The left derivative at the endpoint does not exist and positive-power suspension values can have infinite right slope there; this is the series boundary convention.
--   - reading: The general verification upper envelope is denoted max. → It is an extended supremum; the pointwise inequality is unchanged.; reason: An arbitrary verification pair need not have a finite attained maximum. Actual optimal-contract attainment is asserted separately.
--   - encoding: Processes and equations are written without null-set conventions. → Utilities are actual conditional expectations; drift statements use predictable versions dt-a.e., jump statements use indistinguishable versions.; reason: This gives the standard stochastic interpretation and preserves all right-continuous binary deviations, both contract states and the infinite time horizon.
-- source:
--   Cao, Sun, Tian, Punish Underperformance with Suspension: Optimal Dynamic Contracts in the Presence of Switching Cost, Management Science (2024), doi:10.1287/mnsc.2023.4845, authors' manuscript (2023-03-15), SHA-256 39e9a1afe4665462f93250c221173be577581eb346a2679660d4de54a49b3304, p. 16, Theorem 1

import Mathlib
import Definitions.Def_SuspensionContract_HighCostC2_Supplement_Verification

open scoped NNReal

namespace SuspensionContract.HighCostC2.Supplement

theorem theorem_1 (P : Params) (hP : P.Standing) (VI V0 : ℝ → ℝ)
    (hV : VerificationPair P VI V0) :
    (∀ G : Contract, Feasible P G → ∀ w : ℝ, 0 ≤ w →
      agentUtility P G (complying P G) = (w : EReal) →
      principalUtility P G ≤ ((V0 w - w : ℝ) : EReal)) ∧
    optimalValue P ≤ ⨆ w : {w : ℝ // 0 ≤ w}, ((V0 w.val - w.val : ℝ) : EReal) := by sorry

end SuspensionContract.HighCostC2.Supplement
