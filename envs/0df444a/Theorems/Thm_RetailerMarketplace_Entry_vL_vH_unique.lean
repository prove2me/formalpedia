-- Prove2me | Theorems.Thm_RetailerMarketplace_Entry_vL_vH_unique
-- name    : RetailerMarketplace.Entry.vL_vH_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:10:44.675171+00:00
-- url     : https://prove2.me/theorems/3e918757-e5cc-4823-8d22-91a15b80feff
-- title:
--   Proof of Proposition 2, p. 15 — above k̲ the system π^SBM_M(v_L) = Δπ(v_H), (1 − G(v_H)) + (G(v_T) − G(v_L)) = k has a unique solution
-- statement:
--   Let $c>0$, $f\in[0,1)$, $\lambda\in[\tfrac12,1]$, $k\in[0,1]$, and let $\mu$ be a probability measure on $\mathbb R$ with $\mu((-\infty,c))=0$, absolutely continuous with respect to Lebesgue measure, and charging every nonempty open interval of $[c,\infty)$; $G(v)=\mu((-\infty,v])$. Suppose $k>\underline k=1-G(v^*)$. Then the system
--   $$\pi_M^{SBM}(v_L)=\Delta\pi_M^{SBMT-SBT}(v_H),\qquad (1-G(v_H))+(G(v_T)-G(v_L))=k$$
--   has a solution with $c\le v_L\le v_T\le v_H\le v^*$, it is the only solution in that range, and when $k<1$ it satisfies $v_L<v_T<v_H$.
--
--   The pair $(v_L,v_H)$ equalizes $M$'s marginal profitability of entry across nonmarketplace and marketplace products while using all capacity: it is the pair of thresholds of Mode II in Proposition 2.
--
--   **Formalization Note** The proof writes $v_L<v_T$ and $v_H\in(v_T,v^*)$; at $k=1$ the solution is $v_L=c$, $v_H=v_T$, so the bounds are closed and the strict ones are stated for $k<1$. Full support on $[c,\infty)$ is the reading of $G^{-1}$ in (3) and is what makes the solution unique. Integrability of $v$ is not needed here and not assumed.
-- source:
--   Hervas-Drane & Shelegia, Retailer-Led Marketplaces, Management Science (2025), Articles in Advance, doi:10.1287/mnsc.2023.00315, p. 15 (PDF p. 17), proof of Proposition 2, the two equations for v_L and v_H

import Mathlib
import Definitions.Def_RetailerMarketplace_Entry_Model

open MeasureTheory

namespace RetailerMarketplace.Entry

/-- Proof of Proposition 2, p. 15: when capacity exceeds `k̲ = 1 - G(v*)`, the system
`π_M^SBM(v_L) = Δπ_M^{SBMT-SBT}(v_H)`, `(1 - G(v_H)) + (G(v_T) - G(v_L)) = k`
has exactly one solution with `c ≤ v_L ≤ v_T ≤ v_H ≤ v*`, and for `k < 1` it has `v_L < v_T < v_H`. -/
theorem vL_vH_unique (μ : Measure ℝ) [IsProbabilityMeasure μ] (c f lam k : ℝ) (hc : 0 < c)
    (hf : f ∈ Set.Ico (0 : ℝ) 1) (hlam : lam ∈ Set.Icc (1 / 2 : ℝ) 1)
    (hk : k ∈ Set.Icc (0 : ℝ) 1) (hsupp : μ (Set.Iio c) = 0) (hac : μ ≪ volume)
    (hfull : ∀ a b : ℝ, c ≤ a → a < b → 0 < μ (Set.Ioo a b)) (hkbar : kbar μ c f lam < k) :
    ∃ vL vH : ℝ,
      (c ≤ vL ∧ vL ≤ vT c f ∧ vT c f ≤ vH ∧ vH ≤ vStar c f lam ∧
        piSBM c vL = dPi c f lam vH ∧
        (1 - G μ vH) + (G μ (vT c f) - G μ vL) = k) ∧
      (∀ vL' vH' : ℝ, c ≤ vL' → vL' ≤ vT c f → vT c f ≤ vH' → vH' ≤ vStar c f lam →
        piSBM c vL' = dPi c f lam vH' →
        (1 - G μ vH') + (G μ (vT c f) - G μ vL') = k → vL' = vL ∧ vH' = vH) ∧
      (k < 1 → vL < vT c f ∧ vT c f < vH) := by sorry

end RetailerMarketplace.Entry
