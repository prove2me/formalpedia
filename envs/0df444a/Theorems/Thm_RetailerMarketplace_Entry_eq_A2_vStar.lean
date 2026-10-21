-- Prove2me | Theorems.Thm_RetailerMarketplace_Entry_eq_A2_vStar
-- name    : RetailerMarketplace.Entry.eq_A2_vStar
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T04:10:49.431181+00:00
-- url     : https://prove2.me/theorems/1c6ea64f-2aac-4006-9218-faa44a11d21c
-- title:
--   Proof of Proposition 2, p. 14, (A.2) — v* = cλ/((1 − f)²(λ − f(1 − λ))) solves Δπ(v*) = π^SBM_M(v_T), v* ≥ v_T
-- statement:
--   Let $c>0$, $f\in[0,1)$, $\lambda\in[\tfrac12,1]$, $v_T=c/(1-f)$ and
--   $$v^*=\frac{c\lambda}{(1-f)^2(\lambda-f(1-\lambda))}\qquad\text{(A.2)}.$$
--   Then
--   1. $\Delta\pi_M^{SBMT-SBT}(v^*)=\pi_M^{SBM}(v_T)=v_T-c$;
--   2. $v^*\ge v_T$, and $v^*>v_T$ when $f>0$;
--   3. at $f=0$, $v^*=v_T=c$;
--   4. every marketplace product $v\ge v^*$ is strictly more profitable to enter than any nonmarketplace product $u<v_T$: $\pi_M^{SBM}(u)<\Delta\pi_M^{SBMT-SBT}(v)$.
--
--   The capacity threshold of Proposition 2 is $\underline k=1-G(v^*)$, the mass of the products $v\ge v^*$ (defined in the model file).
--
--   **Formalization Note** The page's "products with $v\ge v^*$ provide a higher marginal profitability of entry under SBMT than products $v<v_T$ under SBM" is item 4.
-- source:
--   Hervas-Drane & Shelegia, Retailer-Led Marketplaces, Management Science (2025), Articles in Advance, doi:10.1287/mnsc.2023.00315, p. 14 (PDF p. 16), proof of Proposition 2, display (A.2) and the definition of k̲

import Mathlib
import Definitions.Def_RetailerMarketplace_Entry_Model

namespace RetailerMarketplace.Entry

/-- Proof of Proposition 2, p. 14, (A.2): `v* = cλ/((1 - f)^2 (λ - f(1 - λ)))` satisfies
`Δπ_M^{SBMT-SBT}(v*) = π_M^SBM(v_T)`, `v* ≥ v_T` (strictly when `f > 0`), `v* = v_T = c` at `f = 0`,
and every marketplace product `v ≥ v*` has a strictly higher marginal profitability of entry under
SBMT than any nonmarketplace product `u < v_T` under SBM. -/
theorem eq_A2_vStar (c f lam : ℝ) (hc : 0 < c) (hf : f ∈ Set.Ico (0 : ℝ) 1)
    (hlam : lam ∈ Set.Icc (1 / 2 : ℝ) 1) :
    dPi c f lam (vStar c f lam) = piSBM c (vT c f) ∧
      vT c f ≤ vStar c f lam ∧
      (0 < f → vT c f < vStar c f lam) ∧
      (f = 0 → vStar c f lam = c ∧ vT c f = c) ∧
      (∀ v u : ℝ, vStar c f lam ≤ v → u < vT c f → piSBM c u < dPi c f lam v) := by sorry

end RetailerMarketplace.Entry
