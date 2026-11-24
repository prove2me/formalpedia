-- Prove2me | Theorems.Thm_UnfairML_Coverage_Supplement_theorem_5_false
-- name    : UnfairML.Coverage.Supplement.theorem_5_false
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T00:38:54.440324+00:00
-- url     : https://prove2.me/theorems/dec7c79f-ddb1-4705-9148-34c42114c1f5
-- title:
--   Theorem 5 (corrected: refuted as printed, negation stated) — the risk condition βp/αp ≥ r̂ does not imply that the general fairness notion lowers protected coverage
-- statement:
--   Theorem 5 (p. 28) asserts: for every $\theta\ge1$, if $\beta_p/\alpha_p\ge\hat r$ then $\phi_p(\theta)\le\phi_p(1)$, where $\phi_p(\theta)=\theta\gamma_r s^*(\theta)/(1-\gamma_p s^*(\theta))$ is the protected coverage rate (19) at the optimal effort $s^*(\theta)$ of (13) and $\hat r$ is the threshold printed above (20). This statement is false. It is not the case that for all parameters satisfying the standing assumptions of §3.1 ($\alpha,\beta>0$, $0<d_r<d_p<1$, $\alpha_r\le\beta_r$, $0<\gamma_p<\gamma_r$) and the low-loss case $\beta_p\le\alpha_p+\alpha_r$, every cost $\tau(s)=ks/(1-\gamma_r s)$ with $k=\alpha_r\gamma_r+\sigma^2A$ in the range of p. 23, every $\theta>1$, and all efforts $s_1, s_\theta$ that globally maximize (13) at $1$ and at $\theta$ (both over the feasible branch efforts and over the whole interval $[0,1/(2\gamma_r)]$),
--   $$\frac{\beta_p}{\alpha_p}\ge\hat r(\theta,s_1,s_\theta)\ \Longrightarrow\ \frac{\theta\gamma_r s_\theta}{1-\gamma_p s_\theta}\le\frac{\gamma_r s_1}{1-\gamma_p s_1}.$$
--   A witness is $\alpha=1$, $\beta=2$, $d_r=1/3$, $d_p=7/20$, $\gamma_r=1$, $\gamma_p=1/2$, $k=5/6$ ($\sigma=\sqrt5/3$), $\theta=9/5$, with $s_1=(1-\sqrt5/3)/(1-\sqrt5/6)\approx0.4059$ and $s_\theta=(1-5/\sqrt{39})/(1-5/(2\sqrt{39}))\approx0.3324$: there $\hat r\approx-0.402<14/13=\beta_p/\alpha_p$, but $\phi_p(9/5)\approx0.718>0.509\approx\phi_p(1)$.
--
--   The refutation holds for the narrowest reading of the source (special cost, cost range, low loss, interior unique optima), so it refutes every broader one, including general convex increasing costs.
--
--   Differences from the source:
--   - correction: Theorem 5 asserts the implication → the Lean states its negation (a counterexample exists within every source assumption); reason: the claim is false as printed, see DISPROOF.md
--   - correction: Table 1 calls α and β utility and dis-utility without explicitly imposing positivity → α>0 and β>0 through the published Standing predicate; reason: the economic utility/loss interpretation and the brief require positive primitives; restricting the universally quantified claim only strengthens its refutation
--   - reading: "∀θ ≥ 1, if βp/αp ≥ r̂" with r̂ depending on θ → the condition is read pointwise in θ, as in the derivation "This condition simplifies to (20)"; θ = 1 (where r̂ is 0/0) is excluded by 1 < θ, which only strengthens the refutation
--   - reading: s∗(θ) is the optimal learning effort → global maxima of (13) on the branch-feasible efforts and on [0,1/(2γr)]; reason: both readings of the optimization domain are covered at once
-- source:
--   Fu, Aseri, Singh & Srinivasan, “Un”Fair Machine Learning Algorithms, SSRN working paper 3408275 (version of 25 Mar 2021), p. 28, Theorem 5, eq. (20); pp. 25–27, eqs. (13), (19); p. 23 cost range

import Mathlib
import Definitions.Def_UnfairML_Coverage_Supplement_GeneralCoverage

namespace UnfairML.Coverage.Supplement

/-- Theorem 5, p. 28, is false as printed. Its claim — for every `θ ≥ 1`, `βp/αp ≥ r̂` implies
`φp(θ) ≤ φp(1)` — fails even under every standing assumption, the low-loss case, the special cost
`τ(s) = ks/(1 − γr s)` with `k` in the cost range of p. 23, `θ > 1`, and optimal efforts that are
global maxima of (13) both on the branch's feasible set and on the whole effort interval. -/
theorem theorem_5_false :
    ¬ ∀ (P : Params) (k σ θ s₁ sθ : ℝ),
      P.Standing → P.LowLoss → CostRange P k σ → 1 < θ →
      IsOptGeneral P (tau P k) 1 s₁ →
      (∀ t ∈ Set.Icc (0 : ℝ) P.sMax, generalProfit P (tau P k) 1 t ≤ generalProfit P (tau P k) 1 s₁) →
      IsOptGeneral P (tau P k) θ sθ →
      (∀ t ∈ Set.Icc (0 : ℝ) P.sMax, generalProfit P (tau P k) θ t ≤ generalProfit P (tau P k) θ sθ) →
      rhat P θ s₁ sθ ≤ P.βp / P.αp →
      protCoverageGeneral P θ sθ ≤ protCoverageGeneral P 1 s₁ := by sorry

end UnfairML.Coverage.Supplement
