-- Prove2me | Theorems.Thm_SystemicDiv_SellOff_proposition_4_2
-- name    : SystemicDiv.SellOff.proposition_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:24:24.63442+00:00
-- url     : https://prove2.me/theorems/153c75ef-9da0-4131-b912-63e3ebffec2f
-- title:
--   Proposition 4.2, p. 18 — the single-bank optimum lies in $(1/2, \gamma_2/(\gamma_1+\gamma_2))$ and decreases in $\ell$
-- statement:
--   Let there be one bank and two assets with $0 < \gamma_1 < \gamma_2$, and let the shock $Z = (Z_1, Z_2)$ satisfy Assumption 3.3 and $E\|Z\|^2 < \infty$. Write the bank's portfolio as $(\pi_{1,1}, 1 - \pi_{1,1})$.
--
--   1. If $S_1$ is convex on $\Pi$ and $(\pi^S_{1,1}, 1 - \pi^S_{1,1})$ minimizes $S_1$ on $\Pi$, then
--   $$\pi^S_{1,1} \in \Big(\tfrac12, \tfrac{\gamma_2}{\gamma_1+\gamma_2}\Big).$$
--   2. The optimal weight is strictly decreasing in the distance to liquidation: if two banks have $\ell < \ell'$, both have convex $S$, and $\pi^S_{1,1}(\ell)$, $\pi^S_{1,1}(\ell')$ are their optimal weights, then $\pi^S_{1,1}(\ell') < \pi^S_{1,1}(\ell)$.
--
--   A bank close to its threshold tilts towards the liquid asset; a bank far from it diversifies more.
--
--   **Formalization Note.** Asset $1$ is index `0`. Added hypotheses: $E\|Z\|^2 < \infty$, and each bank liquidates with positive probability under every portfolio in $\Pi$. The second one is necessary. For a shock law of bounded support (e.g. uniform on a disc, which meets Assumption 3.3) and a bank with $\ell$ close to $1$, $S_1$ vanishes on an interval around $1/2$, and $1/2$ itself is a minimizer. The two banks of part 2 may differ in $w$ and $\lambda_M$; $S$ scales by $(\lambda_M w)^2$, so the optimal weight depends on $\ell$ only.
-- source:
--   Capponi & Weber, Systemic Portfolio Diversification, SSRN 3345399 (version of June 15, 2023), p. 18, Proposition 4.2; proof pp. 43–44

import Mathlib
import Definitions.Def_SystemicDiv_SellOff_Model

open MeasureTheory

namespace SystemicDiv.SellOff

/-- Proposition 4.2, p. 18 (one bank, two assets, `0 < γ_1 < γ_2`, Assumption 3.3): if `S_1` is convex
on `Π` and `(t, 1 − t)` minimizes `S_1` on `Π`, then `t ∈ (1/2, γ_2/(γ_1+γ_2))`; and the optimal
weight `π^S_{1,1}(ℓ)` is strictly decreasing in the distance to liquidation `ℓ`.
Added: finite second moment of `Z`, and the bank liquidates with positive probability under every
admissible portfolio (without it `S_1` can vanish identically near `(1/2, 1/2)`). -/
theorem proposition_4_2 (μ : Measure (Shock 2)) [IsProbabilityMeasure μ]
    (hZ : Assumption33 μ) (hM2 : SecondMoment μ)
    (γ : Fin 2 → ℝ) (hγ : 0 < γ 0 ∧ γ 0 < γ 1) :
    (∀ b : Bank, b.Standing →
        (∀ p ∈ stdSimplex ℝ (Fin 2), 0 < μ {z | Liquidates b (portRet p z)}) →
        ConvexOn ℝ (stdSimplex ℝ (Fin 2)) (S μ γ b) →
        ∀ t : ℝ, IsBenchmark μ γ b (two t) → 1 / 2 < t ∧ t < γ 1 / (γ 0 + γ 1)) ∧
    (∀ b b' : Bank, b.Standing → b'.Standing →
        (∀ p ∈ stdSimplex ℝ (Fin 2), 0 < μ {z | Liquidates b (portRet p z)}) →
        (∀ p ∈ stdSimplex ℝ (Fin 2), 0 < μ {z | Liquidates b' (portRet p z)}) →
        b.ell < b'.ell →
        ConvexOn ℝ (stdSimplex ℝ (Fin 2)) (S μ γ b) →
        ConvexOn ℝ (stdSimplex ℝ (Fin 2)) (S μ γ b') →
        ∀ t t' : ℝ, IsBenchmark μ γ b (two t) → IsBenchmark μ γ b' (two t') → t' < t) := by sorry

end SystemicDiv.SellOff
