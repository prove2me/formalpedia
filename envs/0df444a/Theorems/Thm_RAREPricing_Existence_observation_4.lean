-- Prove2me | Theorems.Thm_RAREPricing_Existence_observation_4
-- name    : RAREPricing.Existence.observation_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:25:44.359867+00:00
-- url     : https://prove2.me/theorems/9bd424e9-4ed9-4e25-bef3-6fbc500cdded
-- title:
--   Observation 4 — R_j ≤ νp_j; full sale when Σp ≤ β; total revenue ≥ νβ when Σp ≥ β
-- statement:
--   Let $I$ be a market, fix the setting with its constants $\nu,\beta$ ($\nu=1,\beta=B$ rivalrous; $\nu=n,\beta=b_{\min}$ non-rivalrous), let $p\in\mathbb R^m_{\ge0}$ and $x\in\mathrm{Dem}(p)$. Then
--   1. $R_j(p,x)\le\nu p_j$ for every seller $j$;
--   2. if $\sum_jp_j\le\beta$, every good is fully sold, $\sum_ix_{i,j}=\nu$ for every $j$, and hence $R_j(p,x)=\nu p_j$ for every $j$;
--   3. if $\sum_jp_j\ge\beta$ then
--   $$R_{\mathrm{all}}(p,x)\ge\nu\beta .$$
--
--   These are the only properties of the revenue functions the existence proof uses; on the simplex $\beta\Delta_m$ they give $R_j(p)=\nu p_j$ and $R_{\mathrm{all}}(p)=\nu\beta=B/\kappa$.
--
--   Differences from the source:
--   - encoding: "every good is fully sold" → $\sum_ix_{i,j}=\nu$ for every $j$; reason: unit supply sold out ($\nu=1$) in the rivalrous setting, every buyer taking the whole good ($\sum_i x_{i,j}=n$ with $x_{i,j}\le1$) in the non-rivalrous one.
--   - encoding: $R_{\mathrm{all}}(p)\ge\nu\beta$, with $R_{\mathrm{all}}(p)$ the value common to all demanded allocations (Observation 2) → $R_{\mathrm{all}}(p,x)\ge\nu\beta$ for the given $x\in\mathrm{Dem}(p)$; reason: the paper's notation unfolded, the value does not depend on the demanded allocation.
-- source:
--   Chaudhury, Garg, Huang, Sharma, RARE: Response-Aware Rational Equilibrium in Budget-Constrained Pricing Games, STOC 2027 submission (manuscript sha256 e9bb863f…), pp. 15–16 (PDF 17–18), Observation 4

import Mathlib
import Definitions.Def_RAREPricing_Existence_Model

namespace RAREPricing.Existence

theorem observation_4 {n m : ℕ} (M : Market n m) (s : Setting) (p : Fin m → ℝ) (hp : 0 ≤ p)
    (x : Fin n → Fin m → ℝ) (hx : x ∈ Dem M s p) :
    (∀ j, revenue p x j ≤ nu M s * p j) ∧
    (∑ j, p j ≤ beta M s →
      (∀ j, ∑ i, x i j = nu M s) ∧ ∀ j, revenue p x j = nu M s * p j) ∧
    (beta M s ≤ ∑ j, p j → nu M s * beta M s ≤ totalRevenue p x) := by sorry

end RAREPricing.Existence
