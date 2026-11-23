-- Prove2me | Theorems.Thm_SalesRebate_NoIncreasing_Supplement_lemma_2
-- name    : SalesRebate.NoIncreasing.Supplement.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T03:21:16.745607+00:00
-- url     : https://prove2.me/theorems/adb999c1-b011-4aa7-a97f-5ef3702b3d12
-- title:
--   Lemma 2, p. 17 (PDF 17) — if r̂ has spread rmax − rmin ≤ √(2π)σϵσ/σθ, the expected payoff of adoption vi − p + E[r̂ | vi] is increasing in vi
-- statement:
--   Let $(\theta,\sigma_\theta,\sigma_\epsilon)$ be a valid model of §II, $\sigma^2=\sigma_\epsilon^2+\sigma_\theta^2$, $p$ a price, and $\hat r:\mathbb R\to[0,p]$ a measurable reward (a function of the quality) whose largest and smallest values satisfy
--   $$r_{\max}-r_{\min}\ \le\ \sqrt{2\pi}\,\frac{\sigma_\epsilon\sigma}{\sigma_\theta}.\tag{11}$$
--   Then the expected payoff of adoption of a consumer with valuation $x$,
--   $$x\ \mapsto\ x-p+\mathbb E_{v\mid v_i=x}[\hat r(v)],$$
--   is (weakly) increasing in $x$, where $\mathbb E_{v\mid v_i=x}$ is the expectation under the posterior $N(\tau x+(1-\tau)\theta,\sigma_v^2)$.
--
--   Under (11) the purchase payoff crosses zero once, so the equilibrium constraints (1) reduce to the indifference equation at the cutoff; this is why the spread-constrained problem of Theorem 3 needs only that equation, and why its optimum is feasible for problem (3) (Theorem 5 i).
--
--   Differences from the source:
--   - reading: the expected payoff of adoption, assuming a monotone symmetric (threshold) strategy, is increasing with the valuations → Monotone (fun x => x − p + E_{v|vi=x}[r̂(v)]) for the given reward r̂ of the quality; reason: under a threshold strategy the reward is a fixed function r̂ of the quality (p. 10) and the payoff of adoption at valuation vi is vi − p + E_{v|vi}[r̂(v)]; 'increasing' is weak, the convention of the published mission, and is what the single-crossing argument (p. 18) uses
--   - encoding: rmax − rmin ≤ √(2π)σϵσ/σθ (minimum and maximum reward paid) → ∀ v w, r̂ v − r̂ w ≤ spreadBound M; reason: equivalent to sup r̂ − inf r̂ ≤ bound, without real sSup/sInf
--   - encoding: the reward program r̂ (an element of L∞(R; [0, p]), p. 10) → IsAdmissibleReward p r̂ (measurable, values in [0, p]); reason: the paper's rewards are bounded measurable functions with values in [0, p]; measurability makes the conditional expectation meaningful
--   - encoding: standing assumptions of §II → hM : M.Valid (σθ, σε > 0); reason: the Gaussian laws presuppose positive deviations
--   - generalization: the standing Assumption-1 market price p → an arbitrary price p for which the bounded reward hypotheses hold; reason: the purchase payoff differs by the additive constant −p, which does not affect monotonicity; the proof on pp. 29–30 or 33–34 uses no price-optimality assumption. Specializing to a market price recovers every source instance
-- source:
--   Ajorlou, Jadbabaie, Sales-Based Rebate Design, arXiv:1902.09646v4, p. 17–18, Lemma 2 and (11)

import Mathlib
import Definitions.Def_BlackScholesModel_Core
import Definitions.Def_SalesRebate_NoIncreasing_Setting
import Definitions.Def_SalesRebate_NoIncreasing_Supplement_Problems

namespace SalesRebate.NoIncreasing.Supplement

open MeasureTheory ProbabilityTheory BlackScholesModel Filter Topology

theorem lemma_2 (M : Model) (hM : M.Valid) (p : ℝ) (rhat : ℝ → ℝ)
    (hrhat : IsAdmissibleReward p rhat) (hspread : ∀ v w, rhat v - rhat w ≤ spreadBound M) :
    Monotone (fun x => x - p + M.condReward rhat x) := by sorry

end SalesRebate.NoIncreasing.Supplement
