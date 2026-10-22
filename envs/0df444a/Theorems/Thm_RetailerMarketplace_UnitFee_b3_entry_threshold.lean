-- Prove2me | Theorems.Thm_RetailerMarketplace_UnitFee_b3_entry_threshold
-- name    : RetailerMarketplace.UnitFee.b3_entry_threshold
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T06:28:57.719985+00:00
-- url     : https://prove2.me/theorems/99aeb82f-bde8-45ce-93ff-694762ee0e0a
-- title:
--   App. B.3, p. 18 — with a unit fee, T profits iff v > v_T = (c + t)/(1 − f)
-- statement:
--   Fix a marginal cost $c>0$, an ad valorem fee $f\in[0,1)$, a per-unit fee $t\ge0$ and a steering share $\lambda\in[1/2,1]$, and write
--   $$v_T=\frac{c+t}{1-f}.$$
--   For every product valuation $v$:
--   1. the third-party seller's profit in an SBT market is positive exactly above the threshold,
--   $$(1-f)v-c-t>0 \iff v>v_T;$$
--   2. her margin in an SBMT market, with the price $\bar p_T=\frac{\lambda v+(1-\lambda)(c+t)}{1-f(1-\lambda)}$ of (B.1), is positive exactly above the same threshold,
--   $$\bar p_T(1-f)-c-t>0\iff v>v_T;$$
--   3. she enters (does not make a loss) exactly from the threshold on: $v(1-f)\ge c+t \iff v\ge v_T$.
--
--   This is the entry analysis of Appendix B.3: a per-unit fee acts on the seller like a marginal-cost increase, so the whole entry analysis of the baseline model carries over with $v_T$ redefined as $(c+t)/(1-f)$.
--
--   **Formalization Note.** The page's claims are strict ("positive profits", "$v>(c+t)/(1-f)$"), and items 1–2 state them strictly; item 3 records the zero-profit entry convention used for the marketplace set, as in the paper's Lemma 1. The SBMT claim concerns the margin $\bar p_T(1-f)-c-t$ printed on the page, not the profit $(1-\lambda)(\cdot)$, which vanishes identically at $\lambda=1$. $\lambda\ge1/2$ is the paper's standing Assumption 1; the equivalence in item 2 uses only $\lambda>0$.
-- source:
--   Hervas-Drane & Shelegia, Retailer-Led Marketplaces, Management Science (2025), Articles in Advance, doi:10.1287/mnsc.2023.00315, p. 18 (PDF p. 20), App. B.3, display (B.1) and the paragraph after it

import Mathlib
import Definitions.Def_RetailerMarketplace_UnitFee_Model

namespace RetailerMarketplace.UnitFee

/-- App. B.3, p. 18: with a unit fee `t`, T's SBT profit `(1 - f) v - c - t` and her SBMT margin
`p̄_T (1 - f) - c - t` (with `p̄_T` from (B.1)) are positive exactly when `v > v_T = (c + t)/(1 - f)`;
and T's entry set (entry at zero profit) is `[v_T, ∞)`. -/
theorem b3_entry_threshold (c f t lam : ℝ) (hc : 0 < c) (hf : f ∈ Set.Ico (0 : ℝ) 1)
    (ht : 0 ≤ t) (hlam : lam ∈ Set.Icc (1 / 2 : ℝ) 1) (v : ℝ) :
    (0 < piSBT_T c f t v ↔ vT c f t < v) ∧
    (0 < pbarT c f t lam v * (1 - f) - c - t ↔ vT c f t < v) ∧
    (v ∈ mp c f t ↔ vT c f t ≤ v) := by sorry

end RetailerMarketplace.UnitFee
