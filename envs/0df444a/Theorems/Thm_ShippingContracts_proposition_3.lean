-- Prove2me | Theorems.Thm_ShippingContracts_proposition_3
-- name    : ShippingContracts.proposition_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:54:21.414981+00:00
-- url     : https://prove2.me/theorems/4fa2c0d2-83d0-4c11-8eef-55d08df1daef
-- title:
--   Proposition 3 — the shipper's optimal capacity is $c^0$ if $c^0\le q^*$ and $q^*$ otherwise
-- statement:
--   Let $0<u\le u'$ and let the demand $D\ge0$ have finite mean and a c.d.f. $F$ continuous and strictly increasing on $\{x\ge0:F(x)<1\}$. Then a point $c^0\ge0$ with
--   $$F(c^0)=\frac{u'-u}{u'}$$
--   exists, and for every contract $(\nu,p_o,p_u)$ (risk penalty or flat rate), every reservation $r$, every inventory $q\ge0$ and such a $c^0$, the capacity $c$ maximizes the shipper's profit (4.5) over $c\ge0$ if and only if
--   $$c=c^0\ \text{ when } c^0\le q,\qquad c=q\ \text{ when } q<c^0.$$
--
--   So the shipper never builds more regular capacity than the seller's inventory, and builds less when the emergency premium $u'-u$ is small.
--
--   **Formalization Note** The paper states the result at the seller's response $q^*$; here $q\ge0$ is arbitrary, which covers both contracts.
--
--   Differences from the source:
--   - reading: D with density f and c.d.f. F, both continuous and differentiable; F⁻¹ used as an inverse with F⁻¹(0) = 0, integrals from 0 (p. 9; App. p. 3) → μ a probability measure with D ≥ 0 a.s., finite mean, F = cdf μ continuous and strictly increasing on {x ≥ 0 : F(x) < 1}; reason: these are the properties the paper's use of F⁻¹ on [0, 1), of integrals from 0 and of E[D] in the objectives requires; F(0) = 0 follows.
--   - generalization: a density f of D exists → no density assumed; reason: every law with a density and a c.d.f. strictly increasing on its support from 0 is an instance, so the statement specializes to the paper's.
--   - reading: u > 0 not stated in the theorem (it is used in the proofs, "= u > 0", App. p. 2) → 0 < u as a hypothesis; reason: without it the fractile (u' − u)/u' is undefined at u' = 0 and the shipper's cost need not increase beyond q.
--   - encoding: F⁻¹(t) → a point x ≥ 0 with F(x) = t; reason: under the demand law this point exists and is unique for every t ∈ [0, 1), and every fractile used is in [0, 1).
--   - encoding: the optimal decisions r*, q*, c*, (c*_FB, q*_FB) → argmax predicates SellerBR, ShipperBR, FirstBest over r, q, c ≥ 0; reason: the sequence of events (p. 10) makes each decision a maximizer of (3.2), (4.5), (5.7) over nonnegative quantities.
--   - generalization: the standing price assumption p > c > s → not assumed; reason: the shipper's capacity problem does not involve p, c, s; adding it gives the paper's setting.
--   - generalization: at the seller's response q* to the contract → every inventory q ≥ 0, every reservation r and every contract; reason: the seller's response is one such q, so the statement specializes.
-- source:
--   Song–Zhao, Supply Chain Coordination for E-Commerce: Risk Penalty vs. Flat Rate (SSRN manuscript 3129499, titled 'Supply Chain Integration for Online Shopping Holidays: Risk Penalty vs. Flat Rate'; version of record MSOM 2021, doi:10.1287/msom.2021.1008), Proposition 3, pp. 15–16 (PDF 15–16); proof App. p. 2 (PDF 31)

import Mathlib
import Definitions.Def_ShippingContracts_Model

open MeasureTheory ProbabilityTheory

namespace ShippingContracts

/-- **Proposition 3** (the shipper's optimal capacity), Song–Zhao, SSRN 3129499, pp. 15–16
(PDF 15–16); proof App. p. 2 (PDF 31). Under `0 < u ≤ u'` and the demand law, `c⁰ = F⁻¹((u' − u)/u')`
exists, and for every contract `κ`, every reservation `r` and every inventory `q ≥ 0`, the
shipper's optimal capacities are: `c* = c⁰` if `c⁰ ≤ q`, and `c* = q` otherwise.

**Formalization Note.** `c⁰` is any `x ≥ 0` with `F x = (u' − u)/u'` (it is unique). The paper's
`q*` is the seller's response; the statement holds for every `q ≥ 0` and every `r`, so it covers
both contracts. -/
theorem proposition_3 (P : Params) (hSh : P.Shipping)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hD : DemandLaw μ) :
    (∃ c0 : ℝ, 0 ≤ c0 ∧ cdf μ c0 = (P.uE - P.u) / P.uE) ∧
    ∀ (κ : Contract) (r q c0 : ℝ), 0 ≤ q → 0 ≤ c0 → cdf μ c0 = (P.uE - P.u) / P.uE →
      ∀ cap : ℝ, ShipperBR P μ κ r q cap ↔ ((c0 ≤ q ∧ cap = c0) ∨ (q < c0 ∧ cap = q)) := by sorry

end ShippingContracts
