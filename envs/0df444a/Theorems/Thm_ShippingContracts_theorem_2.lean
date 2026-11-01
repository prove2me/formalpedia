-- Prove2me | Theorems.Thm_ShippingContracts_theorem_2
-- name    : ShippingContracts.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:54:25.748057+00:00
-- url     : https://prove2.me/theorems/cba864e3-9d66-4b88-b0fe-3065971f772e
-- title:
--   Theorem 2 — at $p_o=0$ or $p_u=0$ the risk penalty is equivalent to the flat rate
-- statement:
--   Let $p>c>s$ and let the demand $D\ge0$ have finite mean and a c.d.f. $F$ continuous and strictly increasing on $\{x\ge0:F(x)<1\}$. Let $\kappa=(\nu,p_o,p_u)$ be a feasible contract ($u\le\nu$, $0\le p_u\le c_u-\nu$, $0\le p_o\le\nu$) with $p_o=0$ or $p_u=0$, and let $\kappa_0=(\nu,0,0)$ be the flat rate with the same base rate. Then:
--
--   1. every best response $(r,q)$ of the seller to $\kappa$ is a best response to $\kappa_0$;
--   2. for every best response $(r_0,q)$ of the seller to $\kappa_0$ there is a reservation $r$ such that $(r,q)$ is a best response to $\kappa$;
--   3. at every best response $(r,q)$ of the seller to $\kappa$, the shipper's profit (4.5) under $\kappa$ equals its flat-rate profit (4.6) at every capacity $c$, and the seller's profit (3.2) under $\kappa$ equals its profit under $\kappa_0$.
--
--   Hence the shipper's problem under the risk penalty with one penalty equal to zero is the shipper's problem under the flat rate: the seller's inventory response and the shipper's payoff are the same. This is why the paper treats "$p_o=0$ or $p_u=0$" as the flat rate from here on.
--
--   Differences from the source:
--   - reading: D with density f and c.d.f. F, both continuous and differentiable; F⁻¹ used as an inverse with F⁻¹(0) = 0, integrals from 0 (p. 9; App. p. 3) → μ a probability measure with D ≥ 0 a.s., finite mean, F = cdf μ continuous and strictly increasing on {x ≥ 0 : F(x) < 1}; reason: these are the properties the paper's use of F⁻¹ on [0, 1), of integrals from 0 and of E[D] in the objectives requires; F(0) = 0 follows.
--   - generalization: a density f of D exists → no density assumed; reason: every law with a density and a c.d.f. strictly increasing on its support from 0 is an instance, so the statement specializes to the paper's.
--   - encoding: the optimal decisions r*, q*, c*, (c*_FB, q*_FB) → argmax predicates SellerBR, ShipperBR, FirstBest over r, q, c ≥ 0; reason: the sequence of events (p. 10) makes each decision a maximizer of (3.2), (4.5), (5.7) over nonnegative quantities.
--   - reading: "the shipper's problem under the risk penalty contract is equivalent to the shipper's problem under the flat rate contract" → items 1–3: the seller's best-response inventories coincide, and the shipper's profit is the flat-rate profit at every capacity; reason: the shipper's problem is the maximization of (4.5) given the seller's response; equal responses and equal payoffs make the two problems the same.
--   - generalization: the standing model of §4, including Assumption 2 (u' ≥ u) and u > 0 → neither assumed; reason: Theorem 2 is about the seller's response and the penalty term, which do not involve u, u' (feasibility still requires u ≤ ν); adding them gives the paper's setting.
--   - generalization: statement about the shipper's problem only → also the seller's profit under κ equals its flat-rate profit at every best response; reason: an additional conclusion; dropping it gives the paper's claim, and the proof of Theorem 8 uses it.
-- source:
--   Song–Zhao, Supply Chain Coordination for E-Commerce: Risk Penalty vs. Flat Rate (SSRN manuscript 3129499, titled 'Supply Chain Integration for Online Shopping Holidays: Risk Penalty vs. Flat Rate'; version of record MSOM 2021, doi:10.1287/msom.2021.1008), Theorem 2, p. 16 (PDF 16); proof App. pp. 2–3 (PDF 31–32)

import Mathlib
import Definitions.Def_ShippingContracts_Model

open MeasureTheory ProbabilityTheory

namespace ShippingContracts

/-- **Theorem 2** (partial equivalence), Song–Zhao, SSRN 3129499, p. 16 (PDF 16); proof
App. pp. 2–3 (PDF 31–32). Under `p > c > s` and the demand law, let `κ = (ν, p_o, p_u)` be
feasible with `p_o = 0` or `p_u = 0`, and `κ₀ = (ν, 0, 0)` the flat rate with the same `ν`. Then
1. every seller best response `(r, q)` to `κ` is a best response to `κ₀`;
2. every inventory `q` of a best response to `κ₀` is, with a suitable reservation `r`, a best
   response to `κ`;
3. at every seller best response `(r, q)` to `κ`, the shipper's profit (4.5) equals the flat-rate
   profit (4.6) at every capacity, and the seller's profit equals its flat-rate profit.

**Formalization Note.** Items 1–3 are what "the shipper's problem under the risk penalty is
equivalent to the shipper's problem under the flat rate" means for the follower's response and
the leader's payoff; the equality of the seller's profits is added (the proof of Theorem 8
needs it). -/
theorem theorem_2 (P : Params) (hPr : P.Prices)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hD : DemandLaw μ)
    (κ : Contract) (hκ : Feasible P κ) (hflat : κ.po = 0 ∨ κ.pu = 0) :
    (∀ r q : ℝ, SellerBR P μ κ r q → SellerBR P μ ⟨κ.nu, 0, 0⟩ r q) ∧
    (∀ r₀ q : ℝ, SellerBR P μ ⟨κ.nu, 0, 0⟩ r₀ q → ∃ r : ℝ, SellerBR P μ κ r q) ∧
    (∀ r q : ℝ, SellerBR P μ κ r q →
      (∀ cap : ℝ, shipperProfit P μ κ r q cap = shipperProfit P μ ⟨κ.nu, 0, 0⟩ r q cap) ∧
      sellerProfit P μ κ r q = sellerProfit P μ ⟨κ.nu, 0, 0⟩ r q) := by sorry

end ShippingContracts
