-- Prove2me | Theorems.Thm_PELiquidity_Primary_eq11
-- name    : PELiquidity.Primary.eq11
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T08:06:56.468682+00:00
-- url     : https://prove2.me/theorems/d967fb15-27d4-4b19-84c1-7c71feddf4de
-- title:
--   (11), p. 16 — the LPs' break-even return is 1 + r(λ, δ) = 1/(1 − λ(1 − δ)), decreasing in δ
-- statement:
--   Let $\lambda\in(0,1)$ be the probability of the liquidity shock and $\delta\in(0,1)$ the LP's discount factor after the shock. Without a secondary market, a unit of private equity promising the expected return $\bar R$ is worth $(1-\lambda)\bar R+\lambda\delta\bar R$ to the LP, while cash is worth $1$. Then
--
--   1. the LP is indifferent between private equity and cash exactly at
--   $$\bar R=1+r(\lambda,\delta)=\frac{1}{1-\lambda(1-\delta)};$$
--   2. the map $\delta\mapsto 1+r(\lambda,\delta)$ is strictly decreasing on $(0,1)$.
--
--   The net return $r(\lambda,\delta)$ is the illiquidity premium LPs demand; LPs more tolerant of the shock demand a lower premium. This is the price of capital that Lemma 1 and Proposition 1 take as given.
-- source:
--   Maurin, Robinson & Strömberg, A Theory of Liquidity in Private Equity, working paper (draft of December 2020), p. 16, (11)

import Mathlib
import Definitions.Def_PELiquidity_Primary_Setting

namespace PELiquidity.Primary

/-- (11): without a secondary market, the LPs' break-even return solves
`(1 - λ) R̄ + λ δ R̄ = 1`, i.e. `R̄ = 1 + r(λ, δ) = 1 / (1 - λ (1 - δ))`, and it is strictly
decreasing in the tolerance `δ ∈ (0, 1)`. -/
theorem eq11 (lam δ : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (∀ Rb : ℝ, (1 - lam) * Rb + lam * (δ * Rb) = 1 ↔ Rb = grossReturn lam δ) ∧
    StrictAntiOn (grossReturn lam) (Set.Ioo 0 1) := by sorry

end PELiquidity.Primary
