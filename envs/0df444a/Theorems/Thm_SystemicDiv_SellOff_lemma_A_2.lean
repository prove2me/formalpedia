-- Prove2me | Theorems.Thm_SystemicDiv_SellOff_lemma_A_2
-- name    : SystemicDiv.SellOff.lemma_A_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:24:30.165459+00:00
-- url     : https://prove2.me/theorems/f1df1f4b-484d-43dd-afc1-a4821ee5f08d
-- title:
--   Lemma A.2, p. 45 — for small distances to liquidation, $\partial^2 P/\partial\pi_{i,1}\partial\pi_{j,1} > 0$
-- statement:
--   Let $K = 2$, let the shock satisfy Assumption 3.3 and $E\|Z\|^2 < \infty$, and fix $\gamma_1, \gamma_2 > 0$, total assets $w_i$ and thresholds $\lambda_{M,i}$ for $N$ banks. Then there is $\bar\ell > 0$ such that, whenever every bank satisfies the standing assumptions and $\ell_i \le \bar\ell$ (Assumption 3.7),
--   $$\frac{\partial^2 P}{\partial \pi_{i,1}\,\partial \pi_{j,1}}(\pi) > 0 \qquad \text{for all } i \ne j \text{ and } \pi \in \Pi^N,$$
--   where each $\pi_m = (\pi_{m,1}, 1 - \pi_{m,1})$.
--
--   The cross-partials of the potential are positive, so each bank's best response decreases in the other banks' holding of asset 1: portfolio choices are strategic substitutes.
--
--   **Formalization Note.** The mixed partial is the derivative in $t_j$ of the derivative in $t_i$ of $t \mapsto P((t_m, 1-t_m)_m)$, at a point with every $t_m \in [0,1]$. Lean's `deriv` is $0$ where no derivative exists, so the strict inequality also asserts differentiability. $\bar\ell$ is chosen after $\mu$, $\gamma$, $w$ and $\lambda_M$ and before the leverages. Asset $1$ is index `0`.
-- source:
--   Capponi & Weber, Systemic Portfolio Diversification, SSRN 3345399 (version of June 15, 2023), p. 45, Lemma A.2; Assumption 3.7, p. 16

import Mathlib
import Definitions.Def_SystemicDiv_SellOff_Model

open MeasureTheory

namespace SystemicDiv.SellOff

/-- Lemma A.2, p. 45 (`K = 2`, Assumptions 3.3 and 3.7): for a sufficiently small `ℓ̄`, if every bank
has `ℓ_i ≤ ℓ̄`, then `∂²P/∂π_{i,1}∂π_{j,1}(π) > 0` for all `i ≠ j` and all `π ∈ Π^N`. The profile is
`π_i = (t_i, 1 − t_i)`; the mixed partial is the iterated derivative in `t_i` then `t_j`. -/
theorem lemma_A_2 {N : ℕ} (μ : Measure (Shock 2)) [IsProbabilityMeasure μ]
    (hZ : Assumption33 μ) (hM2 : SecondMoment μ)
    (γ : Fin 2 → ℝ) (hγ : ∀ k, 0 < γ k) (w levM : Fin N → ℝ) :
    ∃ ellbar > 0, ∀ B : Fin N → Bank,
      (∀ i, (B i).Standing ∧ (B i).ell ≤ ellbar ∧ (B i).w = w i ∧ (B i).levM = levM i) →
      ∀ t : Fin N → ℝ, (∀ i, t i ∈ Set.Icc (0 : ℝ) 1) → ∀ i j : Fin N, i ≠ j →
        0 < deriv (fun s => deriv (fun r =>
              Pot μ B γ (fun m => two (Function.update (Function.update t j s) i r m))) (t i))
            (t j) := by sorry

end SystemicDiv.SellOff
