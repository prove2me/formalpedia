-- Prove2me | Theorems.Thm_RAREPricing_Existence_observation_2
-- name    : RAREPricing.Existence.observation_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:25:44.387688+00:00
-- url     : https://prove2.me/theorems/67fefe3c-d5c1-4e24-a667-99ca622cff39
-- title:
--   Observation 2 — closed form of the total revenue on the demand set (both settings)
-- statement:
--   Let $I$ be a market (the definition item: $n\ge1$, $m\ge2$, $b_i>0$, utilities continuous, strictly monotone on $[0,1]^m$ with $u_i(0)=0$) and $p\in\mathbb R^m_{\ge0}$. Put $F(y):=\sum_{i=1}^n\min(b_i,y)$. Then:
--   1. (non-rivalrous) for every $x\in\mathrm{DemNR}(p)$, $R_{\mathrm{all}}(p,x)=F\big(\sum_jp_j\big)$, and $F(y)\le\min(B,ny)$ for every real $y$;
--   2. (rivalrous) for every $x\in\mathrm{DemR}(p)$,
--   $$R_{\mathrm{all}}(p,x)=\min\Big(B,\sum_{j=1}^mp_j\Big);$$
--   3. in either setting, $R_{\mathrm{all}}(p,x)\le B$ for every $x\in\mathrm{Dem}(p)$.
--
--   The total revenue is thus a function of the price sum alone; this is what makes the pricing game behave like a fixed-sum game at high prices.
--
--   Differences from the source:
--   - reading: $F(y)\le\min(B,ny)$ with the domain of $y$ unstated → stated for every real $y$; reason: the inequality is a property of $F$ and holds for every real $y$; at $y=\sum_jp_j$ it is the printed instance.
-- source:
--   Chaudhury, Garg, Huang, Sharma, RARE: Response-Aware Rational Equilibrium in Budget-Constrained Pricing Games, STOC 2027 submission (manuscript sha256 e9bb863f…), p. 15 (PDF 17), Observation 2

import Mathlib
import Definitions.Def_RAREPricing_Existence_Model

namespace RAREPricing.Existence

theorem observation_2 {n m : ℕ} (M : Market n m) (p : Fin m → ℝ) (hp : 0 ≤ p) :
    (∀ x ∈ DemNR M p, totalRevenue p x = ∑ i, min (M.b i) (∑ j, p j)) ∧
    (∀ y : ℝ, ∑ i, min (M.b i) y ≤ min M.totalBudget ((n : ℝ) * y)) ∧
    (∀ x ∈ DemR M p, totalRevenue p x = min M.totalBudget (∑ j, p j)) ∧
    (∀ s : Setting, ∀ x ∈ Dem M s p, totalRevenue p x ≤ M.totalBudget) := by sorry

end RAREPricing.Existence
