-- Prove2me | Theorems.Thm_RobustSPA_AllDist_pointwise_regret_le_inv_e
-- name    : RobustSPA.AllDist.pointwise_regret_le_inv_e
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:28:39.146193+00:00
-- url     : https://prove2.me/theorems/3b6d70b3-2dd6-4f88-92ce-84532544b3d8
-- title:
--   Proof of Proposition 4, Cases 1–3, p. App-8 — the pointwise regret of SPA(Φ*) is at most 1/e, with equality when v^(1) ≥ 1/e ≥ v^(2)
-- statement:
--   Let $n \ge 1$ and let $\Phi^*$ be the reserve distribution of Proposition 4, whose CDF is $0$ on $(-\infty, 1/e]$, $\log p + 1$ on $[1/e, 1]$ and $1$ above $1$. For $v \in [0,1]^n$ write $R_n(\Phi^*, v) = v^{(1)} - \sum_i p_i(v)$ for the regret of $\mathrm{SPA}(\Phi^*)$ at $v$. Then
--   $$R_n(\Phi^*, v) \le \frac1e,$$
--   and more precisely:
--
--   1. (Case 1) if $v^{(1)} \ge 1/e \ge v^{(2)}$, then $R_n(\Phi^*, v) = 1/e$;
--   2. (Case 2) if $v^{(2)} > 1/e$, then $R_n(\Phi^*, v) = -v^{(2)}\log v^{(2)} < 1/e$;
--   3. (Case 3) if $v^{(1)} < 1/e$, then $R_n(\Phi^*, v) = v^{(1)}$.
--
--   Every point of the support of $\mathbf F^{*,k}$ has $v^{(2)} = 0$ and $v^{(1)} \in [1/e, 1]$, so Case 1 says that $\mathrm{SPA}(\Phi^*)$ attains its largest pointwise regret on the support of Nature's worst case: this is the half $R_n(m^*, \mathbf F) \le R_n(m^*, \mathbf F^*)$ of the saddle inequality.
--
--   **Formalization Note** The page prints the lower limit of the Case 1 integral as $e^{-1/\lambda}$ and evaluates it at $1/e$; the statement uses $1/e$. The page's "equality holds when $v$ is on the support of $\mathbf F^{*,1}$" is stated for the whole region of Case 1, which contains that support. The CDF of $\Phi^*$ is given as a hypothesis on the law.
-- source:
--   Anunrojwong, Balseiro & Besbes, On the Robustness of Second-Price Auctions in Prior-Independent Mechanism Design, arXiv:2204.10478v5, p. App-8, Proof of Proposition 4, Cases 1–3

import Mathlib
import Definitions.Def_RobustSPA_AllDist_Setting
open MeasureTheory

namespace RobustSPA.AllDist

/-- Proof of Proposition 4, Cases 1–3, p. App-8: the pointwise regret of `SPA(Φ*)` is at most
`1/e`, with equality when `v^(2) ≤ 1/e ≤ v^(1)`. -/
theorem pointwise_regret_le_inv_e (n : ℕ) (hn : 0 < n) (ρ : ProbabilityMeasure ℝ)
    (hρ : ∀ t, cdfOf ρ t = PhiE t) (v : Fin n → ℝ) (hv : v ∈ cube n) :
    top v - ∑ i, (SPA (ρ : Measure ℝ)).p i v ≤ Real.exp (-1) ∧
    (second v ≤ Real.exp (-1) → Real.exp (-1) ≤ top v →
      top v - ∑ i, (SPA (ρ : Measure ℝ)).p i v = Real.exp (-1)) ∧
    (Real.exp (-1) < second v →
      top v - ∑ i, (SPA (ρ : Measure ℝ)).p i v = -(second v * Real.log (second v)) ∧
      -(second v * Real.log (second v)) < Real.exp (-1)) ∧
    (top v < Real.exp (-1) → top v - ∑ i, (SPA (ρ : Measure ℝ)).p i v = top v) := by sorry

end RobustSPA.AllDist
