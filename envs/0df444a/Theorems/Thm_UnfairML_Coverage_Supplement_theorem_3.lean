-- Prove2me | Theorems.Thm_UnfairML_Coverage_Supplement_theorem_3
-- name    : UnfairML.Coverage.Supplement.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T00:36:41.520316+00:00
-- url     : https://prove2.me/theorems/715ec50e-589b-42a7-9892-e636e110dd5f
-- title:
--   Theorem 3 (corrected: positive utilities and policy-specific counts) — protected success rate is strictly higher under ET, for every convex increasing cost
-- statement:
--   Use the §3.1 parameters with $\alpha,\beta>0$, $0<d_r<d_p<1$, $\alpha_r\le\beta_r$, $0<\gamma_p<\gamma_r$ and the low-loss condition $\beta_p\le\alpha_p+\alpha_r$ of the main text (p. 17). Let $\tau$ be any convex nondecreasing learning cost on $[0,1/(2\gamma_r)]$. Take globally optimal ET and EO policies (profit (1) with cost $\tau$, thresholds in $[0,1]$) whose thresholds are the canonical ones selected in (4) and (10):
--   $$c^{ET}=1-\gamma_r s^{ET},\quad c_r^{EO}=1-\gamma_r s^{EO},\quad
--   c_p^{EO}=1-\frac{\gamma_r s^{EO}(1-\gamma_p s^{EO})}{1-\gamma_r s^{EO}}.$$
--   Define $N_S=(1-d_p)\min\{(1-c_p)/(1-\gamma_p s),1\}$, $N_F=d_p\max\{(1-\gamma_p s-c_p)/(1-\gamma_p s),0\}$ and $\delta_p=N_S/(N_S+N_F)$ separately for each policy. If the EO policy accepts some protected candidate ($N_S^{EO}+N_F^{EO}>0$, so that $\delta_p^{EO}$ is defined), then the ET policy also accepts some protected candidate and
--   $$\delta_p^{ET}>\delta_p^{EO}.$$
--   This compares the good fraction among protected applicants accepted by the two policies. It does not assume Theorem 2's special cost or its risk inequality. At $\beta_p=\alpha_p+\alpha_r$, (10)'s first branch is retained. For the special cost $\tau(s)=ks/(1-\gamma_r s)$ with $k$ in the range of p. 23, the positive-acceptance hypothesis holds automatically, since that range gives $s^{EO}>0$.
--
--   Differences from the source:
--   - correction: Table 1 calls α and β utility and dis-utility without explicitly imposing positivity → α>0 and β>0 through the published Standing predicate; reason: the economic utility/loss interpretation and the brief require positive primitives; cases α≤0 or β≤0 are excluded
--   - reading: §3.1 uses the half-open effort interval → the closed interval [0,1/(2γr)] of Appendix A p. 43; reason: Appendix A specifies this boundary convention and it retains endpoint optima
--   - encoding: threshold decisions have their feasible score ranges → thresholds lie in [0,1] and global optimality ranges over the full feasible box; reason: these are the admissible probability thresholds of (1), not additional stationarity assumptions
--   - reading: τ is convex increasing → ConvexOn and MonotoneOn on the admissible effort interval; reason: increasing is read as nondecreasing, with no differentiability or strict-concavity requirement
--   - correction: p. 45 prints a stray d in the ET failure count and ET subscripts in the EO denominator → d means dp and the EO denominator is NS_EO+NF_EO; reason: p. 21 defines success rate using the same policy, and the EO counts and final closed form on p. 45 determine these notation repairs
--   - reading: optimal thresholds are selected by (4) and (10) → globally optimal policies use their displayed first-branch thresholds including the equality case; reason: the source selects that branch even when alternative threshold optima tie
--   - reading: δ is the fraction of successful acceptances among all accepted candidates (p. 21) → hypothesis that the EO policy accepts a positive mass of protected candidates; positivity of the ET acceptances is a conclusion; reason: δEO is undefined (0/0) otherwise; under the p. 23 special cost and range this holds automatically, so no source case where δ is defined is excluded
-- source:
--   Fu, Aseri, Singh & Srinivasan, “Un”Fair Machine Learning Algorithms, SSRN working paper 3408275 (version of 25 Mar 2021), p. 24, Theorem 3; p. 14 cost scope; p. 21 definition; p. 45 proof

import Mathlib
import Definitions.Def_UnfairML_Coverage_Supplement_Success
import Definitions.Def_UnfairML_Coverage_Supplement_CostModel

namespace UnfairML.Coverage.Supplement

/-- Theorem 3, p. 24, for every convex increasing learning cost (p. 14: only Theorem 2 uses the
special cost), at the policies selected by (4) and (10), including the first branch of (10) when
`βp = αp + αr`. The EO success rate is defined only when EO accepts someone (`hpos`); the ET
acceptance count is then positive as a conclusion. -/
theorem theorem_3 (P : Params) (hS : P.Standing) (hL : P.LowLoss)
    (τ : ℝ → ℝ) (hτ : IsLearningCost P τ)
    (sET sEO : ℝ)
    (hET : IsOptETWithCost P τ (1 - P.γr * sET) sET)
    (hEO : IsOptEOWithCost P τ
      (1 - P.γr * sEO * (1 - P.γp * sEO) / (1 - P.γr * sEO))
      (1 - P.γr * sEO) sEO)
    (hpos : 0 < successful P
      (1 - P.γr * sEO * (1 - P.γp * sEO) / (1 - P.γr * sEO)) sEO +
      failed P (1 - P.γr * sEO * (1 - P.γp * sEO) / (1 - P.γr * sEO)) sEO) :
    0 < successful P (1 - P.γr * sET) sET + failed P (1 - P.γr * sET) sET ∧
    successRate P
      (1 - P.γr * sEO * (1 - P.γp * sEO) / (1 - P.γr * sEO)) sEO <
      successRate P (1 - P.γr * sET) sET := by sorry

end UnfairML.Coverage.Supplement
