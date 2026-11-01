-- Prove2me | Theorems.Thm_ShippingContracts_eq_3_4
-- name    : ShippingContracts.eq_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:54:33.468029+00:00
-- url     : https://prove2.me/theorems/20d964d1-6bc9-4036-8cb9-55e19cadab7b
-- title:
--   Eq. (3.4) — under the flat rate the seller's inventory is $q^0_F=F^{-1}\big((c_u-\nu)/((c_u-\nu)+c_o)\big)$ and the reservation is irrelevant
-- statement:
--   Let $p>c>s$, $c_o=c-s$, $c_u=p-c$, and let the demand $D\ge0$ have finite mean and a c.d.f. $F$ continuous and strictly increasing on $\{x\ge0:F(x)<1\}$. Consider the flat rate contract $(\nu,0,0)$ with $\nu\le c_u$ (Assumption 1). Then a point $q\ge0$ with
--   $$F(q)=\frac{c_u-\nu}{(c_u-\nu)+c_o}$$
--   exists, and $(r,q)$ is a best response of the seller, i.e. maximizes $\Pi_{\rm Seller}$ (3.2) over $r,q\ge0$, if and only if $r\ge0$ and $q\ge0$ satisfies this equation. So $q^*_F=q^0_F=F^{-1}\big(\frac{c_u-\nu}{(c_u-\nu)+c_o}\big)$, and $r$ is irrelevant.
--
--   This is the seller's newsvendor response to the flat rate; the shipper's capacity and the coordination results are computed from it.
--
--   **Formalization Note** "$r$ is not a decision variable" is expressed by letting $r\ge0$ be arbitrary.
--
--   Differences from the source:
--   - reading: D with density f and c.d.f. F, both continuous and differentiable; F⁻¹ used as an inverse with F⁻¹(0) = 0, integrals from 0 (p. 9; App. p. 3) → μ a probability measure with D ≥ 0 a.s., finite mean, F = cdf μ continuous and strictly increasing on {x ≥ 0 : F(x) < 1}; reason: these are the properties the paper's use of F⁻¹ on [0, 1), of integrals from 0 and of E[D] in the objectives requires; F(0) = 0 follows.
--   - generalization: a density f of D exists → no density assumed; reason: every law with a density and a c.d.f. strictly increasing on its support from 0 is an instance, so the statement specializes to the paper's.
--   - encoding: F⁻¹(t) → a point x ≥ 0 with F(x) = t; reason: under the demand law this point exists and is unique for every t ∈ [0, 1), and every fractile used is in [0, 1).
--   - encoding: the optimal decisions r*, q*, c*, (c*_FB, q*_FB) → argmax predicates SellerBR, ShipperBR, FirstBest over r, q, c ≥ 0; reason: the sequence of events (p. 10) makes each decision a maximizer of (3.2), (4.5), (5.7) over nonnegative quantities.
--   - generalization: under the flat rate, Assumption 1 (2) ν ≥ p_o gives ν ≥ 0, and the shipper's constraint (p. 15) gives u ≤ ν ≤ c_u → only ν ≤ c_u is assumed (ν may be negative; u does not occur); reason: the seller's newsvendor problem needs only c_u − ν ≥ 0, and the fractile (c_u − ν)/((c_u − ν) + c_o) stays in [0, 1) for every ν ≤ c_u; adding ν ≥ 0 or u ≤ ν gives the paper's setting.
--   - encoding: "r is not a decision variable; thus, it is irrelevant" → every r ≥ 0 is a best response together with q⁰_F; reason: under p_o = p_u = 0 the seller's profit does not depend on r, so the argmax over r ≥ 0 is the whole half-line.
-- source:
--   Song–Zhao, Supply Chain Coordination for E-Commerce: Risk Penalty vs. Flat Rate (SSRN manuscript 3129499, titled 'Supply Chain Integration for Online Shopping Holidays: Risk Penalty vs. Flat Rate'; version of record MSOM 2021, doi:10.1287/msom.2021.1008), eq. (3.4), p. 14 (PDF 14)

import Mathlib
import Definitions.Def_ShippingContracts_Model

open MeasureTheory ProbabilityTheory

namespace ShippingContracts

/-- **Eq. (3.4)** (the seller's inventory under the flat rate), Song–Zhao, SSRN 3129499, p. 14
(PDF 14). Under `p > c > s` and the demand law, for a flat rate `κ = (ν, 0, 0)` with
`ν ≤ c_u` (Assumption 1 (1), p. 11): the seller's best responses are exactly the pairs `(r, q)`
with `r ≥ 0` arbitrary and `q = q⁰_F = F⁻¹((c_u − ν)/((c_u − ν) + c_o))`, i.e. `q ≥ 0`,
`F(q) = (c_u − ν)/((c_u − ν) + c_o)`; and such a `q` exists.

**Formalization Note.** "r is not a decision variable; thus, it is irrelevant" is the clause
"`r ≥ 0` arbitrary". `F⁻¹(t)` is written as "`q ≥ 0` with `F q = t`". -/
theorem eq_3_4 (P : Params) (hPr : P.Prices)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hD : DemandLaw μ) (ν : ℝ) (hν : ν ≤ P.cu) :
    (∃ q : ℝ, 0 ≤ q ∧ cdf μ q = (P.cu - ν) / ((P.cu - ν) + P.co)) ∧
    ∀ r q : ℝ, SellerBR P μ ⟨ν, 0, 0⟩ r q ↔
      (0 ≤ r ∧ 0 ≤ q ∧ cdf μ q = (P.cu - ν) / ((P.cu - ν) + P.co)) := by sorry

end ShippingContracts
