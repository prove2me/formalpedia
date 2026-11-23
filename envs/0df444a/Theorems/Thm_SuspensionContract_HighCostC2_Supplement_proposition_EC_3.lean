-- Prove2me | Theorems.Thm_SuspensionContract_HighCostC2_Supplement_proposition_EC_3
-- name    : SuspensionContract.HighCostC2.Supplement.proposition_EC_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T21:07:53.633505+00:00
-- url     : https://prove2.me/theorems/20639bbd-c6f4-497e-b220-307113208aba
-- title:
--   Proposition EC.3 (corrected: initial switching equality)
-- statement:
--   Let $V_I,V_\emptyset$ satisfy the complete hypotheses of Theorem 1. Suppose a feasible contract's actual continuation utility and predictable jump coefficients satisfy (PK) and every equality (EC.47)–(EC.51), including the initial expectation equality. In addition, require equality of the initial switching gap and its cost: $V_{E_0}(W_0)-V_\emptyset(W_0)=K\mathbf1_{E_0=I}$. For every nonnegative complying utility $w$,
--   $$u(\Gamma^\circ,\bar\nu)=w\quad\Longrightarrow\quad U(\Gamma^\circ)=V_\emptyset(w)-w.$$
--   All five equality conditions are retained, rather than assuming the desired utility identity. This gives attainment of the verification upper bound.
--
--   Differences from the source:
--   - correction: D is called deterministic but only F-adaptedness is written. → The public filtration after initialization contains no noise beyond N and Q.; reason: Adaptedness alone admits an independent Poisson D and falsifies the two-noise PK equation; this implements the intended deterministic control. See DISPROOF.md.
--   - reading: (20) is printed at w≥0 with a left-derivative convention. → The published OptCond uses (20) at w>0 and retains (21),(22) at zero.; reason: The left derivative at the endpoint does not exist and positive-power suspension values can have infinite right slope there; this is the series boundary convention.
--   - correction: EC.49 is imposed only for t>0 although utility (6) charges a start at time zero. → Bind an explicit InitialSwitchEquality premise at t=0, in addition to all five printed equalities.; reason: Starting an equal-rate always-work/termination contract below its tangent threshold satisfies all five displayed conditions but loses K minus the initial value gap. See DISPROOF.md.
--   - encoding: Processes and equations are written without null-set conventions. → Utilities are actual conditional expectations; drift statements use predictable versions dt-a.e., jump statements use indistinguishable versions.; reason: This gives the standard stochastic interpretation and preserves all right-continuous binary deviations, both contract states and the infinite time horizon.
-- source:
--   Cao, Sun, Tian, Punish Underperformance with Suspension: Optimal Dynamic Contracts in the Presence of Switching Cost, Management Science (2024), doi:10.1287/mnsc.2023.4845, authors' manuscript (2023-03-15), SHA-256 39e9a1afe4665462f93250c221173be577581eb346a2679660d4de54a49b3304, p. ec21, Proposition EC.3

import Mathlib
import Definitions.Def_SuspensionContract_HighCostC2_Supplement_Verification

open scoped NNReal

namespace SuspensionContract.HighCostC2.Supplement

theorem proposition_EC_3 (P : Params) (hP : P.Standing) (VI V0 : ℝ → ℝ)
    (hV : VerificationPair P VI V0) (G : Contract) (hG : Feasible P G)
    (H Hq : ℝ≥0 → G.Ω → ℝ)
    (hPK : PromiseKeeping P G (complying P G) H Hq)
    (heq : AttainmentEqualities P G VI V0 H Hq)
    (hinit : InitialSwitchEquality P G VI V0) :
    ∀ w : ℝ, 0 ≤ w → agentUtility P G (complying P G) = (w : EReal) →
      principalUtility P G = ((V0 w - w : ℝ) : EReal) := by sorry

end SuspensionContract.HighCostC2.Supplement
