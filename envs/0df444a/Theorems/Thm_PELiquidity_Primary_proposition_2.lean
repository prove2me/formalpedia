-- Prove2me | Theorems.Thm_PELiquidity_Primary_proposition_2
-- name    : PELiquidity.Primary.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T08:07:43.880272+00:00
-- url     : https://prove2.me/theorems/cfcc6d0d-4bfb-420f-9058-7f263de7bc58
-- title:
--   Proposition 2, p. 22 — without a secondary market, thresholds 0 < μ̲ < μ̄ < 1 characterize the equilibrium; H-LPs earn strictly more when both fund types are raised
-- statement:
--   Fix the model parameters (Assumptions 1–3, 5 strictly for $\delta_L$, 6, and $B\le p(p-q)R$). For a capital share $\mu_H\in(0,1)$ of $H$-LPs consider the private equity market equilibria without a secondary market (Definition 2). There exist thresholds $\underline\mu_H,\bar\mu_H$ with
--   $$0<\underline\mu_H<\bar\mu_H<1$$
--   such that
--
--   1. for every $\mu_H\in(0,1)$ an equilibrium exists;
--   2. if $\mu_H<\underline\mu_H$, every equilibrium raises both $H$-funds and $L$-funds ($\alpha^*_L>0$, $\alpha^*_H>0$), and $H$-LPs earn a strictly higher return than $L$-LPs:
--   $$\bar R^*_{PE,H}>\bar R^*_{PE,L}=1+r(\lambda,\delta_L);$$
--   3. if $\mu_H\ge\underline\mu_H$, every equilibrium raises only $H$-funds: $\alpha^*_L=0$;
--   4. on $[\underline\mu_H,\bar\mu_H]$ the equilibrium $H$-return is strictly decreasing in $\mu_H$: if $\underline\mu_H\le\mu_1<\mu_2\le\bar\mu_H$, then $\bar R^*_{PE,H}$ at $\mu_2$ is strictly below $\bar R^*_{PE,H}$ at $\mu_1$, for any equilibria at the two shares;
--   5. if $\mu_H\ge\bar\mu_H$, every equilibrium has $\bar R^*_{PE,H}=1+r(\lambda,\delta_H)$: $H$-LPs earn exactly their fair liquidity premium.
--
--   Liquidity-tolerant capital is scarce when $\mu_H$ is small, and GPs then pay a premium for it, because $H$-funds avoid the costly acceleration of capital calls that $L$-funds require (Proposition 1). This yields persistent differences in LP returns that do not come from differences in skill.
--
--   **Formalization Note** Item 1 is not printed in the proposition; the proof constructs the equilibrium and concludes that it is unique (p. 49), and it is included so that items 2–5 are not vacuous. The printed statement has "$\mu_H\le\underline\mu_H$" in i) and "$\mu_H\ge\underline\mu_H$" in ii), which conflict at $\mu_H=\underline\mu_H$; the proof (Case 3, $\alpha^*_H(\underline\mu_H)=1$) puts the boundary in ii), so item 2 uses the strict inequality. "Decreasing" is read as strict, as in (C.4). The thresholds are existential, as printed; the appendix gives them explicitly by (C.3) and the indifference equation on p. 48.
-- source:
--   Maurin, Robinson & Strömberg, A Theory of Liquidity in Private Equity, working paper (draft of December 2020), p. 22, Proposition 2; pp. 47–49, Appendix C.3

import Mathlib
import Definitions.Def_PELiquidity_Primary_Setting
import Definitions.Def_PELiquidity_Primary_Market

namespace PELiquidity.Primary

/-- Proposition 2: there are thresholds `0 < μ̲_H < μ̄_H < 1` such that, for every capital
share `μ_H ∈ (0, 1)` of H-LPs, an equilibrium exists; every equilibrium with `μ_H < μ̲_H`
raises both fund types and pays `R̄*_PE,H > R̄*_PE,L = 1 + r(λ, δ_L)`; every equilibrium with
`μ_H ≥ μ̲_H` raises no L-fund; the H-return is strictly decreasing in `μ_H` on
`[μ̲_H, μ̄_H]`; and for `μ_H ≥ μ̄_H` it equals `1 + r(λ, δ_H)`. -/
theorem proposition_2 (P : Params) :
    ∃ muLow muBar : ℝ, 0 < muLow ∧ muLow < muBar ∧ muBar < 1 ∧
      (∀ muH : ℝ, 0 < muH → muH < 1 → ∃ E : Allocation, IsEquilibrium P muH E) ∧
      (∀ (muH : ℝ) (E : Allocation), 0 < muH → muH < muLow → IsEquilibrium P muH E →
          0 < E.αL ∧ 0 < E.αH ∧ E.RL = grossReturn P.lam P.δL ∧ E.RL < E.RH) ∧
      (∀ (muH : ℝ) (E : Allocation), muLow ≤ muH → muH < 1 → IsEquilibrium P muH E →
          E.αL = 0) ∧
      (∀ (mu₁ mu₂ : ℝ) (E₁ E₂ : Allocation), muLow ≤ mu₁ → mu₁ < mu₂ → mu₂ ≤ muBar →
          IsEquilibrium P mu₁ E₁ → IsEquilibrium P mu₂ E₂ → E₂.RH < E₁.RH) ∧
      (∀ (muH : ℝ) (E : Allocation), muBar ≤ muH → muH < 1 → IsEquilibrium P muH E →
          E.RH = grossReturn P.lam P.δH) := by sorry

end PELiquidity.Primary
