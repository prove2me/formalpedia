-- Prove2me | Theorems.Thm_RetailerMarketplace_Entry_proposition_1_sbt
-- name    : RetailerMarketplace.Entry.proposition_1_sbt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:11:32.026982+00:00
-- url     : https://prove2.me/theorems/6ad2cb57-6532-4d07-876e-a58beb6c0b0f
-- title:
--   Proposition 1.2, p. 5 — SBT: in a subgame perfect equilibrium M steers to T, T charges p_T = v and earns (1 − f)v − c, M earns fv
-- statement:
--   Let $c>0$, $f\in[0,1)$ the ad valorem fee, $\lambda\in[0,1]$, and let $v$ be a product market in which the third-party seller $T$ is viable, $v(1-f)\ge c$, supplied by $T$ alone (configuration SBT). $T$ quotes a price $p_T$; $M$ observes it and steers inattentive consumers to $T$ or not, collecting the fee $f$ on $T$'s revenue.
--
--   Then there is a subgame perfect equilibrium $(p_T,\sigma)$ of this game with
--   $$p_T=v,\qquad \sigma(v)=T,\qquad \pi_T^{SBT}=(1-f)v-c,\qquad \pi_M^{SBT}=fv.$$
--
--   This is the second case of Proposition 1: $M$'s fee revenue from a marketplace product he does not enter.
--
--   **Formalization Note** The statement is existence of an equilibrium with this outcome. Uniqueness is not claimed: at $f=0$ $M$ is indifferent between steering choices, and the steering choice affects $T$'s optimal profit.
-- source:
--   Hervas-Drane & Shelegia, Retailer-Led Marketplaces, Management Science (2025), Articles in Advance, doi:10.1287/mnsc.2023.00315, p. 5 (PDF p. 7), Proposition 1, item 2, and the restriction to viable markets v(1 − f) ≥ c stated before it

import Mathlib
import Definitions.Def_RetailerMarketplace_Entry_Model
import Definitions.Def_RetailerMarketplace_Entry_PricingGame

namespace RetailerMarketplace.Entry

/-- Proposition 1.2 (SBT): when only T supplies a viable product `v` (`v(1 - f) ≥ c`), there is a
subgame perfect equilibrium in which T charges `p_T = v`, M steers inattentive consumers to T,
T earns `π_T^SBT = (1 - f) v - c` and M earns `π_M^SBT = f v`. -/
theorem proposition_1_sbt (c f lam v : ℝ) (hc : 0 < c) (hf : f ∈ Set.Ico (0 : ℝ) 1)
    (hlam : lam ∈ Set.Icc (0 : ℝ) 1) (hv : c ≤ v * (1 - f)) :
    ∃ σ : ℝ → Steer, IsSPNE_SBT c f lam v v σ ∧ σ v = Steer.T ∧
      uT_SBT c f lam v v Steer.T = piSBT_T c f v ∧ uM_SBT f lam v v Steer.T = piSBT_M f v := by sorry

end RetailerMarketplace.Entry
