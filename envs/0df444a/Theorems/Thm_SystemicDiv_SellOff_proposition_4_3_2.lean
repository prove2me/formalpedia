-- Prove2me | Theorems.Thm_SystemicDiv_SellOff_proposition_4_3_2
-- name    : SystemicDiv.SellOff.proposition_4_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:24:34.927514+00:00
-- url     : https://prove2.me/theorems/e7010662-0efd-4c2e-8a96-81348504227c
-- title:
--   Proposition 4.3 part (2), p. 19 — with equal distances to liquidation, everyone holding $\pi^S$ is the unique Nash equilibrium
-- statement:
--   Let $N$ banks and $K = 2$ assets satisfy the standing assumptions, with $\gamma_k > 0$, a shock law satisfying Assumption 3.3 with $E\|Z\|^2 < \infty$, and assume the potential $P$ is strictly convex on $\Pi^N$ (Assumption 3.6). Suppose every bank has the same distance to liquidation, $\ell_i = \ell$, and let $\pi^S \in \Pi$ be the single-bank optimal portfolio at distance $\ell$ (a minimizer of $S_i$ on $\Pi$). Then
--   $$\pi^*_i = \pi^S \quad (i = 1,\dots,N)$$
--   is a Nash equilibrium, and it is the unique one.
--
--   With homogeneous banks, the presence of other banks raises costs but does not change portfolio choices; heterogeneity is what drives the systemic diversification of Proposition 4.4.
--
--   **Formalization Note.** Stated for $K = 2$, since $\pi^S$ is the optimum "determined in Proposition 4.2", which has $K = 2$; $N$ is general. Bank 1 and asset 1 are index `0`. Banks may differ in $w_i$ and $\lambda_{M,i}$ as long as their $\ell_i$ agree. $S_i$ is then a positive multiple of a common function, and $\pi^S$ is assumed to minimize each $S_i$. Added: $E\|Z\|^2 < \infty$.
-- source:
--   Capponi & Weber, Systemic Portfolio Diversification, SSRN 3345399 (version of June 15, 2023), p. 19, Proposition 4.3 (2); proof p. 44

import Mathlib
import Definitions.Def_SystemicDiv_SellOff_Model

open MeasureTheory

namespace SystemicDiv.SellOff

/-- Proposition 4.3 part (2), p. 19 (Assumptions 3.3 and 3.6): if all banks have the same distance to
liquidation `ℓ` and `π^S` is the single-bank optimal portfolio at distance `ℓ` (Proposition 4.2,
so `K = 2`), then the profile in which every bank holds `π^S` is the unique Nash equilibrium. -/
theorem proposition_4_3_2 {N : ℕ} (μ : Measure (Shock 2)) [IsProbabilityMeasure μ]
    (hZ : Assumption33 μ) (hM2 : SecondMoment μ)
    (γ : Fin 2 → ℝ) (hγ : ∀ k, 0 < γ k)
    (B : Fin N → Bank) (hB : ∀ i, (B i).Standing) (ℓ : ℝ) (hℓ : ∀ i, (B i).ell = ℓ)
    (h36 : StrictConvexOn ℝ (Admissible N 2) (Pot μ B γ))
    (piS : Fin 2 → ℝ) (hS : ∀ i, IsBenchmark μ γ (B i) piS) :
    IsNash μ B γ (fun _ => piS) ∧
      ∀ π : Fin N → Fin 2 → ℝ, IsNash μ B γ π → π = fun _ => piS := by sorry

end SystemicDiv.SellOff
