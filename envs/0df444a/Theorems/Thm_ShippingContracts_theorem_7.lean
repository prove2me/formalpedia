-- Prove2me | Theorems.Thm_ShippingContracts_theorem_7
-- name    : ShippingContracts.theorem_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:54:28.346418+00:00
-- url     : https://prove2.me/theorems/70e7270c-bdba-42de-b4a4-841da7470d2f
-- title:
--   Theorem 7 — the flat rate coordinates iff $\nu=u'$ (case a) or $\nu=\frac{c_o+c_u}{c_o+u}u\le u'$ (case b)
-- statement:
--   Throughout, $p>c>s$ are the selling price, procurement cost and salvage value, $c_o=c-s$ and $c_u=p-c$ the seller's overage and underage costs, $0<u\le u'$ the unit costs of regular and emergency shipping capacity, and $D\ge0$ the demand, with finite mean and a c.d.f. $F$ that is continuous and strictly increasing on $\{x\ge0: F(x)<1\}$. $S=\min(q,D)$ is the shipment and $x^+=\max(x,0)$.
--
--   Assume moreover $c_u\ge u'$ (Section 5). Let $\kappa=(\nu,p_o,p_u)$ be a feasible contract with $p_o=0$ or $p_u=0$. Then:
--
--   1. if $\dfrac{c_o}{c_u-u'}<\dfrac{u}{u'-u}$, the contract coordinates the supply chain if and only if $\nu=u'$;
--   2. if $\dfrac{c_o}{c_u-u'}\ge\dfrac{u}{u'-u}$, the contract coordinates the supply chain if and only if
--   $$\nu=\frac{c_o+c_u}{c_o+u}\cdot u,$$
--   and this rate is at most $u'$.
--
--   Here "coordinates" means that the seller and the shipper have best responses and every pair of best responses yields the first-best capacity and inventory. The coordinating rates depend only on the cost parameters, not on the demand distribution.
--
--   **Formalization Note** The switch condition is used multiplied out, $c_o(u'-u)<u(c_u-u')$.
--
--   Differences from the source:
--   - reading: D with density f and c.d.f. F, both continuous and differentiable; F⁻¹ used as an inverse with F⁻¹(0) = 0, integrals from 0 (p. 9; App. p. 3) → μ a probability measure with D ≥ 0 a.s., finite mean, F = cdf μ continuous and strictly increasing on {x ≥ 0 : F(x) < 1}; reason: these are the properties the paper's use of F⁻¹ on [0, 1), of integrals from 0 and of E[D] in the objectives requires; F(0) = 0 follows.
--   - generalization: a density f of D exists → no density assumed; reason: every law with a density and a c.d.f. strictly increasing on its support from 0 is an instance, so the statement specializes to the paper's.
--   - reading: u > 0 not stated in the theorem (it is used in the proofs, "= u > 0", App. p. 2) → 0 < u as a hypothesis; reason: without it the fractile (u' − u)/u' is undefined at u' = 0 and the shipper's cost need not increase beyond q.
--   - encoding: c_o/(c_u − u') < u/(u' − u) → c_o (u' − u) < u (c_u − u'); reason: equivalent when both denominators are positive; at a zero denominator it agrees with the convention a/0 = +∞ for a > 0, and the 0/0 case u = u' = c_u falls in case b, where the closed forms give q = c = 0.
--   - encoding: the optimal decisions r*, q*, c*, (c*_FB, q*_FB) → argmax predicates SellerBR, ShipperBR, FirstBest over r, q, c ≥ 0; reason: the sequence of events (p. 10) makes each decision a maximizer of (3.2), (4.5), (5.7) over nonnegative quantities.
--   - reading: "the flat rate coordinates the supply chain" → Coordinates: the seller and the shipper have best responses, and every pair of best responses is first best; reason: Theorem 5's last sentence describes coordination as the parties choosing the first best to maximize their profits; the existence clause excludes vacuous coordination.
-- source:
--   Song–Zhao, Supply Chain Coordination for E-Commerce: Risk Penalty vs. Flat Rate (SSRN manuscript 3129499, titled 'Supply Chain Integration for Online Shopping Holidays: Risk Penalty vs. Flat Rate'; version of record MSOM 2021, doi:10.1287/msom.2021.1008), Theorem 7, p. 19 (PDF 19); proof App. p. 6 (PDF 35)

import Mathlib
import Definitions.Def_ShippingContracts_Model

open MeasureTheory ProbabilityTheory

namespace ShippingContracts

/-- **Theorem 7** (coordination under the flat rate), Song–Zhao, SSRN 3129499, p. 19 (PDF 19);
proof App. p. 6 (PDF 35). Under `p > c > s`, `0 < u ≤ u'`, `c_u ≥ u'` and the demand law, let
`κ = (ν, p_o, p_u)` be feasible with `p_o = 0` or `p_u = 0`.
* Case a (`c_o/(c_u − u') < u/(u' − u)`): `κ` coordinates the supply chain iff `ν = u'`.
* Case b (otherwise): `κ` coordinates the supply chain iff `ν = ((c_o + c_u)/(c_o + u))·u`, and
  this rate is `≤ u'`.

**Formalization Note.** The switch condition is `CaseA P`, multiplied out. -/
theorem theorem_7 (P : Params) (hPr : P.Prices) (hSh : P.Shipping) (hSC : P.uE ≤ P.cu)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hD : DemandLaw μ)
    (κ : Contract) (hκ : Feasible P κ) (hflat : κ.po = 0 ∨ κ.pu = 0) :
    (CaseA P → (Coordinates P μ κ ↔ κ.nu = P.uE)) ∧
    (¬ CaseA P → ((Coordinates P μ κ ↔ κ.nu = (P.co + P.cu) / (P.co + P.u) * P.u) ∧
      (P.co + P.cu) / (P.co + P.u) * P.u ≤ P.uE)) := by sorry

end ShippingContracts
