-- Prove2me | Theorems.Thm_RetailerMarketplace_Entry_proposition_1_sbmt
-- name    : RetailerMarketplace.Entry.proposition_1_sbmt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:11:23.192991+00:00
-- url     : https://prove2.me/theorems/ec551ec7-4bb0-40e2-8296-19b27ba9c674
-- title:
--   Proposition 1.3, p. 5 — SBMT: subgame perfect equilibrium with p_M = v, p_T = (λv + c(1 − λ))/(1 − f(1 − λ)), unique for 0 < λ < 1 and v(1 − f) > c
-- statement:
--   Let $c>0$, $f\in[0,1)$, $\lambda\in[0,1]$, and let $v$ satisfy $v(1-f)\ge c$. In the sequential pricing game of a product market supplied by both $M$ and $T$ (configuration SBMT), $T$ quotes $p_T$ first; $M$ then quotes $p_M$ and steers inattentive consumers. Write
--   $$\bar p_T=\frac{\lambda v+c(1-\lambda)}{1-f(1-\lambda)}.$$
--
--   1. There is a subgame perfect equilibrium $(p_T,\sigma)$ with $p_T=\bar p_T$ and $\sigma(\bar p_T)=(v,M)$: $M$ charges $p_M=v$ and steers to himself. The equilibrium profits are
--   $$\pi_M^{SBMT}=\lambda(v-c)+(1-\lambda)f\bar p_T,\qquad \pi_T^{SBMT}=(1-\lambda)\big(\bar p_T(1-f)-c\big).$$
--   2. If moreover $0<\lambda<1$ and $v(1-f)>c$, every subgame perfect equilibrium $(p_T,\sigma)$ has $p_T=\bar p_T$ and $\sigma(p_T)=(v,M)$.
--
--   This is the third case of Proposition 1 and supplies $M$'s and $T$'s profits in the markets where both are present.
--
--   **Formalization Note** Proposition 1 says equilibrium outcomes "will be given by" these prices. Existence is stated for every viable $v$. Uniqueness is stated only under $0<\lambda<1$ and $v(1-f)>c$, because it fails otherwise: at $\lambda=1$ $T$'s price does not affect her payoff, at $\lambda=0$ $M$ is indifferent between steering choices, and at $v(1-f)=c$ $T$ is indifferent between $\bar p_T$ and pricing herself out. In the boundary cases $\bar p_T=v$ the tie-breaking rule gives all attentive consumers to $M$, but the equilibrium profits still equal the displayed formulas.
-- source:
--   Hervas-Drane & Shelegia, Retailer-Led Marketplaces, Management Science (2025), Articles in Advance, doi:10.1287/mnsc.2023.00315, p. 5 (PDF p. 7), Proposition 1, item 3; proof of Proposition 1, p. 13 (PDF p. 15)

import Mathlib
import Definitions.Def_RetailerMarketplace_Entry_Model
import Definitions.Def_RetailerMarketplace_Entry_PricingGame

namespace RetailerMarketplace.Entry

/-- Proposition 1.3 (SBMT): when both firms supply a viable product `v` (`v(1 - f) ≥ c`), there is a
subgame perfect equilibrium of the sequential pricing game in which T charges
`p̄_T = (λ v + c(1 - λ))/(1 - f(1 - λ))`, M answers with `p_M = v` and steers inattentive consumers
to himself, and the profits are `π_M^SBMT = λ(v - c) + (1 - λ) f p̄_T` and
`π_T^SBMT = (1 - λ)(p̄_T (1 - f) - c)`. If moreover `0 < λ < 1` and `v(1 - f) > c`, every subgame
perfect equilibrium has this outcome. -/
theorem proposition_1_sbmt (c f lam v : ℝ) (hc : 0 < c) (hf : f ∈ Set.Ico (0 : ℝ) 1)
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1) (hv : c ≤ v * (1 - f)) :
    (∃ σ : ℝ → ℝ × Steer, IsSPNE_SBMT c f lam v (pbarT c f lam v) σ ∧
        σ (pbarT c f lam v) = (v, Steer.M) ∧
        uM c f lam v (pbarT c f lam v) v Steer.M = piSBMT_M c f lam v ∧
        uT c f lam v (pbarT c f lam v) v Steer.M = piSBMT_T c f lam v) ∧
      (0 < lam → lam < 1 → c < v * (1 - f) →
        ∀ (pT : ℝ) (σ : ℝ → ℝ × Steer), IsSPNE_SBMT c f lam v pT σ →
          pT = pbarT c f lam v ∧ σ pT = (v, Steer.M)) := by sorry

end RetailerMarketplace.Entry
