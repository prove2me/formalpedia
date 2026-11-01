-- Prove2me | Theorems.Thm_ShippingContracts_theorem_4
-- name    : ShippingContracts.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:54:24.362778+00:00
-- url     : https://prove2.me/theorems/ca63537a-fd05-421d-b305-8ed7f53ead9f
-- title:
--   Theorem 4 — the supply chain's first-best capacity and inventory in the two cases of the switch condition
-- statement:
--   Throughout, $p>c>s$ are the selling price, procurement cost and salvage value, $c_o=c-s$ and $c_u=p-c$ the seller's overage and underage costs, $0<u\le u'$ the unit costs of regular and emergency shipping capacity, and $D\ge0$ the demand, with finite mean and a c.d.f. $F$ that is continuous and strictly increasing on $\{x\ge0: F(x)<1\}$. $S=\min(q,D)$ is the shipment and $x^+=\max(x,0)$.
--
--   Assume moreover $c_u\ge u'$ (Section 5). A first best $(c^*_{FB},q^*_{FB})$, i.e. a maximizer of the chain's profit (5.7) over $c,q\ge0$, exists, and:
--
--   1. **Case a**, $\dfrac{c_o}{c_u-u'}<\dfrac{u}{u'-u}$: $(c,q)$ is a first best if and only if $c=c^0$ and $q=q^2_{FB}$, where
--   $$F(c^0)=\frac{u'-u}{u'},\qquad F(q^2_{FB})=\frac{c_u-u'}{c_o+(c_u-u')},\qquad c^0,q^2_{FB}\ge0;$$
--   2. **Case b**, $\dfrac{c_o}{c_u-u'}\ge\dfrac{u}{u'-u}$: $(c,q)$ is a first best if and only if $c=q=q^1_{FB}$, where
--   $$F(q^1_{FB})=\frac{c_u-u}{c_o+c_u},\qquad q^1_{FB}\ge0.$$
--
--   In case a emergency capacity is cheap enough that the chain builds regular capacity below its inventory; in case b capacity and inventory are synchronized. This is the benchmark against which coordination is judged.
--
--   **Formalization Note** The switch condition is used multiplied out, $c_o(u'-u)<u(c_u-u')$. Each $F^{-1}(t)$ is a point $x\ge0$ with $F(x)=t$; it is unique.
--
--   Differences from the source:
--   - reading: D with density f and c.d.f. F, both continuous and differentiable; F⁻¹ used as an inverse with F⁻¹(0) = 0, integrals from 0 (p. 9; App. p. 3) → μ a probability measure with D ≥ 0 a.s., finite mean, F = cdf μ continuous and strictly increasing on {x ≥ 0 : F(x) < 1}; reason: these are the properties the paper's use of F⁻¹ on [0, 1), of integrals from 0 and of E[D] in the objectives requires; F(0) = 0 follows.
--   - generalization: a density f of D exists → no density assumed; reason: every law with a density and a c.d.f. strictly increasing on its support from 0 is an instance, so the statement specializes to the paper's.
--   - reading: u > 0 not stated in the theorem (it is used in the proofs, "= u > 0", App. p. 2) → 0 < u as a hypothesis; reason: without it the fractile (u' − u)/u' is undefined at u' = 0 and the shipper's cost need not increase beyond q.
--   - encoding: F⁻¹(t) → a point x ≥ 0 with F(x) = t; reason: under the demand law this point exists and is unique for every t ∈ [0, 1), and every fractile used is in [0, 1).
--   - encoding: c_o/(c_u − u') < u/(u' − u) → c_o (u' − u) < u (c_u − u'); reason: equivalent when both denominators are positive; at a zero denominator it agrees with the convention a/0 = +∞ for a > 0, and the 0/0 case u = u' = c_u falls in case b, where the closed forms give q = c = 0.
--   - encoding: the optimal decisions r*, q*, c*, (c*_FB, q*_FB) → argmax predicates SellerBR, ShipperBR, FirstBest over r, q, c ≥ 0; reason: the sequence of events (p. 10) makes each decision a maximizer of (3.2), (4.5), (5.7) over nonnegative quantities.
-- source:
--   Song–Zhao, Supply Chain Coordination for E-Commerce: Risk Penalty vs. Flat Rate (SSRN manuscript 3129499, titled 'Supply Chain Integration for Online Shopping Holidays: Risk Penalty vs. Flat Rate'; version of record MSOM 2021, doi:10.1287/msom.2021.1008), Theorem 4, p. 17 (PDF 17); proof App. p. 4 (PDF 33)

import Mathlib
import Definitions.Def_ShippingContracts_Model

open MeasureTheory ProbabilityTheory

namespace ShippingContracts

/-- **Theorem 4** (the supply chain's optimal decisions), Song–Zhao, SSRN 3129499, p. 17
(PDF 17); proof App. p. 4 (PDF 33). Under `p > c > s`, `0 < u ≤ u'`, `c_u ≥ u'` and the demand
law, a first best exists, and `(c, q)` is first best exactly when
* case a (`c_o/(c_u − u') < u/(u' − u)`): `c = c⁰` and `q = q²_FB`, i.e. `c ≥ 0`,
  `F(c) = (u' − u)/u'`, `q ≥ 0`, `F(q) = (c_u − u')/(c_o + (c_u − u'))`;
* case b (otherwise): `c = q = q¹_FB`, i.e. `q ≥ 0`, `F(q) = (c_u − u)/(c_o + c_u)`.

**Formalization Note.** `F⁻¹(t)` is written as "`x ≥ 0` with `F x = t`" (unique under
`DemandLaw`); the switch condition is `CaseA P`, multiplied out. -/
theorem theorem_4 (P : Params) (hPr : P.Prices) (hSh : P.Shipping) (hSC : P.uE ≤ P.cu)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hD : DemandLaw μ) :
    (∃ cap q : ℝ, FirstBest P μ cap q) ∧
    (CaseA P → ∀ cap q : ℝ, FirstBest P μ cap q ↔
        (0 ≤ cap ∧ cdf μ cap = (P.uE - P.u) / P.uE ∧
          0 ≤ q ∧ cdf μ q = (P.cu - P.uE) / (P.co + (P.cu - P.uE)))) ∧
    (¬ CaseA P → ∀ cap q : ℝ, FirstBest P μ cap q ↔
        (cap = q ∧ 0 ≤ q ∧ cdf μ q = (P.cu - P.u) / (P.co + P.cu))) := by sorry

end ShippingContracts
