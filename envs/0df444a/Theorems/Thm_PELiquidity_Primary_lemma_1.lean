-- Prove2me | Theorems.Thm_PELiquidity_Primary_lemma_1
-- name    : PELiquidity.Primary.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T08:06:53.418318+00:00
-- url     : https://prove2.me/theorems/4e97be42-45c5-45f2-a2a8-01800cf4b333
-- title:
--   Lemma 1 with (12), pp. 16–17 — Π_GP = pRI − R̄(I − A), so GPs maximize profit by minimizing the expected fee
-- statement:
--   Fix a liquidity tolerance $\delta\in(0,1)$ and the LP break-even promised return $\bar R=1+r(\lambda,\delta)<pR$. The no-default constraint is $1-x\le\delta\bar R$. For every feasible partnership contract $(x,I,f)$ satisfying limited liability, incentive compatibility, $I>A$, and the capital-supply relation (3) $(pR-\bar f)I=\bar R(I-A)$:
--
--   1. the GP's profit is
--   $$\Pi_{GP}=\bar f\,I=pR\,I-\bar R\,(I-A);\qquad(12)$$
--   2. the contract is optimal in (5) if and only if its expected fee $\bar f$ is minimal among all feasible contracts.
--
--   Since the coefficient $pR-\bar R$ on $I$ is positive, the GP prefers a larger fund, and by (3) a larger fund requires a smaller expected fee. Problem (5) therefore reduces to the fee-minimization problem (5b) solved in Lemma 2 and Proposition 1.
--
--   **Formalization Note** The strict cost-of-capital inequality is the shared model's disclosed strengthening of Assumption 5. The lemma is stated at the paper's break-even return and no-default bound.
-- source:
--   Maurin, Robinson & Strömberg, A Theory of Liquidity in Private Equity, working paper (draft of December 2020), pp. 16–17, Lemma 1, (5b), (12)

import Mathlib
import Definitions.Def_PELiquidity_Primary_Setting

namespace PELiquidity.Primary

/-- Lemma 1 with (12): at the LP break-even return `R̄ = 1 + r(λ, δ)` and the
no-default bound `1 - x ≤ δ R̄`, every feasible contract earns
`Π_GP = pR I - R̄ (I - A)`, and an optimal contract minimizes the expected fee. -/
theorem lemma_1 (P : Params) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hCost : grossReturn P.lam δ < P.p * P.R) :
    let Rbar := grossReturn P.lam δ
    let c := δ * Rbar
    (∀ (x I : ℝ) (f : Outcome → ℝ), IsFeasibleContract P Rbar c x I f →
        gpProfit P I f = P.p * P.R * I - Rbar * (I - P.A)) ∧
    (∀ (x I : ℝ) (f : Outcome → ℝ), IsOptimalContract P Rbar c x I f ↔
        (IsFeasibleContract P Rbar c x I f ∧
          ∀ (x' I' : ℝ) (f' : Outcome → ℝ), IsFeasibleContract P Rbar c x' I' f' →
            expectedFee P.p P.p f ≤ expectedFee P.p P.p f')) := by sorry

end PELiquidity.Primary
