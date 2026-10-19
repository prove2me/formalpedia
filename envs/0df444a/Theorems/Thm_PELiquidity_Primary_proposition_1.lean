-- Prove2me | Theorems.Thm_PELiquidity_Primary_proposition_1
-- name    : PELiquidity.Primary.proposition_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T08:06:57.040065+00:00
-- url     : https://prove2.me/theorems/88020821-827d-4518-a569-c2d458c5d1b1
-- title:
--   Proposition 1 with (16)–(17), p. 19 — under the LPs' no-default constraint the optimal early call is [max{x̲, x̂}, x̄] or x̂(λ, δ)
-- statement:
--   Fix the model parameters and an LP discount factor $\delta\in(0,1)$. Write $1+r(\lambda,\delta)=1/(1-\lambda(1-\delta))$, $\hat x(\lambda,\delta)=1-\delta/(1-\lambda(1-\delta))$, $\hat\delta(\lambda)=1-p/(p+(1-\lambda)q)$, $\underline x=q/(p+q)$ and $\bar x=p/(p+q)$. Consider pairs $(x,f)$ with $x\in[0,1]$, $f$ satisfying limited liability and incentive compatibility, and the no-default constraint (5b)
--   $$1-x\le\delta\,(1+r(\lambda,\delta)).$$
--   Call $x$ an optimal early call if some such pair $(x,f)$ minimizes the expected fee $\bar f$ over all such pairs. Then
--
--   1. if $\delta\ge\hat\delta(\lambda)$, the optimal early calls form the interval $\big[\max\{\underline x,\hat x(\lambda,\delta)\},\bar x\big]$, and the minimal expected fee is $p^2B/(p^2-q^2)$;
--   2. if $\delta<\hat\delta(\lambda)$, the only optimal early call is $x^*=\hat x(\lambda,\delta)$, the minimal expected fee is $\frac{pB}{p-q}\hat x(\lambda,\delta)$, and every admissible pair has expected fee strictly above the undistorted fee $p^2B/(p^2-q^2)$.
--
--   The LPs' commitment problem thus forces GPs facing illiquid LPs to call too much capital early, which raises the fee and lowers fund size.
--
--   **Formalization Note** The printed definition "$\bar x=1-\bar x$" is a slip for $\bar x=1-\underline x=p/(p+q)$. The printed "inefficiently accelerates capital calls if $\delta\le\hat\delta(\lambda)$" holds only strictly: at $\delta=\hat\delta(\lambda)$ one has $\hat x=\bar x$ and no distortion, so item 2 is stated for $\delta<\hat\delta(\lambda)$.
-- source:
--   Maurin, Robinson & Strömberg, A Theory of Liquidity in Private Equity, working paper (draft of December 2020), p. 19, Proposition 1, (16), (17)

import Mathlib
import Definitions.Def_PELiquidity_Primary_Setting

namespace PELiquidity.Primary

/-- Proposition 1 with (16)–(17): under the no-default constraint (5b),
`1 - x ≤ δ (1 + r(λ, δ))`, the optimal first calls are `[max {x̲, x̂(λ, δ)}, x̄]` when
`δ ≥ δ̂(λ)` and `x̂(λ, δ)` alone when `δ < δ̂(λ)`; the minimal expected fee is (15) at
the optimal call, and for `δ < δ̂(λ)` every feasible fee strictly exceeds the undistorted
`p²B/(p² - q²)`. -/
theorem proposition_1 (P : Params) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    let c := δ * grossReturn P.lam δ
    let IsFeasibleCall : ℝ → (Outcome → ℝ) → Prop := fun x f =>
      0 ≤ x ∧ x ≤ 1 ∧ 1 - x ≤ c ∧ IsLimitedLiability P.R x f ∧ IsIC P.p P.q P.B x f
    let IsOptimalCall : ℝ → Prop := fun x =>
      ∃ f : Outcome → ℝ, IsFeasibleCall x f ∧
        ∀ (x' : ℝ) (f' : Outcome → ℝ), IsFeasibleCall x' f' →
          expectedFee P.p P.p f ≤ expectedFee P.p P.p f'
    (deltaHat P.p P.q P.lam ≤ δ →
      {x | IsOptimalCall x} = Set.Icc (max (xLow P.p P.q) (xHat P.lam δ)) (xBar P.p P.q) ∧
      IsLeast {v | ∃ x f, IsFeasibleCall x f ∧ v = expectedFee P.p P.p f}
        (P.p ^ 2 * P.B / (P.p ^ 2 - P.q ^ 2))) ∧
    (δ < deltaHat P.p P.q P.lam →
      {x | IsOptimalCall x} = {xHat P.lam δ} ∧
      IsLeast {v | ∃ x f, IsFeasibleCall x f ∧ v = expectedFee P.p P.p f}
        (P.p * P.B / (P.p - P.q) * xHat P.lam δ) ∧
      ∀ (x : ℝ) (f : Outcome → ℝ), IsFeasibleCall x f →
        P.p ^ 2 * P.B / (P.p ^ 2 - P.q ^ 2) < expectedFee P.p P.p f) := by sorry

end PELiquidity.Primary
