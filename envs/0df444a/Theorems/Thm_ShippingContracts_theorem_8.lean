-- Prove2me | Theorems.Thm_ShippingContracts_theorem_8
-- name    : ShippingContracts.theorem_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:54:37.856062+00:00
-- url     : https://prove2.me/theorems/75596dc2-fec6-4f2f-913e-4c3e2218da5a
-- title:
--   Theorem 8 — under the coordinating flat rate both the shipper and the seller earn a nonnegative expected profit, positive exactly when $u<u'$ (shipper) and $u<c_u$ (seller)
-- statement:
--   Throughout, $p>c>s$ are the selling price, procurement cost and salvage value, $c_o=c-s$ and $c_u=p-c$ the seller's overage and underage costs, $0<u\le u'$ the unit costs of regular and emergency shipping capacity, and $D\ge0$ the demand, with finite mean and a c.d.f. $F$ that is continuous and strictly increasing on $\{x\ge0: F(x)<1\}$. $S=\min(q,D)$ is the shipment and $x^+=\max(x,0)$.
--
--   Assume moreover $c_u\ge u'$ (Section 5), and let $\nu_C$ be the coordinating rate of Theorem 7: $\nu_C=u'$ if $\frac{c_o}{c_u-u'}<\frac{u}{u'-u}$, and $\nu_C=\frac{c_o+c_u}{c_o+u}u$ otherwise. Then:
--
--   1. the flat rate $\kappa_C=(\nu_C,0,0)$ is feasible and coordinates the supply chain;
--   2. for every feasible flat-rate contract $\kappa=(\nu,p_o,p_u)$ (that is, $p_o=0$ or $p_u=0$) that coordinates the supply chain, every best response $(r,q)$ of the seller and every best response $c$ of the shipper to it,
--   $$\Pi_{\rm Shipper}(r,q,c)\ge0,\qquad \Pi_{\rm Shipper}(r,q,c)>0\iff u<u',$$
--   $$\Pi_{\rm Seller}(r,q)\ge0,\qquad \Pi_{\rm Seller}(r,q)>0\iff u<c_u.$$
--
--   So, unlike the coordinating risk penalty of Theorem 5, the coordinating flat rate leaves the shipper a positive expected profit whenever emergency capacity costs more than regular capacity, and the seller a positive expected profit whenever its margin exceeds the regular shipping cost.
--
--   **Formalization Note** Clause 2 assumes that $\kappa$ coordinates, not that $\nu=\nu_C$; Theorem 7 makes the two equivalent. The profits are the paper's (4.5) and (3.2) at the parties' best responses.
--
--   Differences from the source:
--   - reading: D with density f and c.d.f. F, both continuous and differentiable; F⁻¹ used as an inverse with F⁻¹(0) = 0, integrals from 0 (p. 9; App. p. 3) → μ a probability measure with D ≥ 0 a.s., finite mean, F = cdf μ continuous and strictly increasing on {x ≥ 0 : F(x) < 1}; reason: these are the properties the paper's use of F⁻¹ on [0, 1), of integrals from 0 and of E[D] in the objectives requires; F(0) = 0 follows.
--   - generalization: a density f of D exists → no density assumed; reason: every law with a density and a c.d.f. strictly increasing on its support from 0 is an instance, so the statement specializes to the paper's.
--   - reading: u > 0 not stated in the theorem (it is used in the proofs, "= u > 0", App. p. 2) → 0 < u as a hypothesis; reason: without it the fractile (u' − u)/u' is undefined at u' = 0 and the shipper's cost need not increase beyond q.
--   - encoding: c_o/(c_u − u') < u/(u' − u) → c_o (u' − u) < u (c_u − u'); reason: equivalent when both denominators are positive; at a zero denominator it agrees with the convention a/0 = +∞ for a > 0, and the 0/0 case u = u' = c_u falls in case b, where the closed forms give q = c = 0.
--   - encoding: the optimal decisions r*, q*, c*, (c*_FB, q*_FB) → argmax predicates SellerBR, ShipperBR, FirstBest over r, q, c ≥ 0; reason: the sequence of events (p. 10) makes each decision a maximizer of (3.2), (4.5), (5.7) over nonnegative quantities.
--   - reading: "the flat rate coordinates the supply chain" → Coordinates: the seller and the shipper have best responses, and every pair of best responses is first best; reason: Theorem 5's last sentence describes coordination as the parties choosing the first best to maximize their profits; the existence clause excludes vacuous coordination.
--   - reading: the flat rate contract: "both po and pu are zero" (p. 10) → κ_C = (ν_C, 0, 0) in clause 1, and every feasible κ with p_o = 0 or p_u = 0 in clause 2; reason: Theorem 7, to which Theorem 8 refers, and the paragraph after Theorem 2 call p_o = 0 or p_u = 0 the flat rate; clause 2 covers the narrower class too.
--   - encoding: "the supply chain coordinating the flat rate contract (as specified in Theorem 7)" → clause 1 for ν_C, and clause 2 for every flat-rate contract that coordinates; reason: by Theorem 7 the coordinating flat-rate contracts are exactly those with ν = ν_C.
--   - reading: "the shipper's (seller's) expected profit can be greater than zero" → both profits are ≥ 0 at every best response; the shipper's is > 0 iff u < u', the seller's is > 0 iff u < c_u; reason: the paper's proof derives ">" in every instance, but its strict step needs c⁰ > 0 or q*_F > 0: at u = u' the shipper's profit is exactly 0, and at u = c_u (which forces u = u' = c_u) both profits are 0; the exact conditions are the strongest true reading.
-- source:
--   Song–Zhao, Supply Chain Coordination for E-Commerce: Risk Penalty vs. Flat Rate (SSRN manuscript 3129499, titled 'Supply Chain Integration for Online Shopping Holidays: Risk Penalty vs. Flat Rate'; version of record MSOM 2021, doi:10.1287/msom.2021.1008), Theorem 8, p. 20 (PDF 20); proof App. pp. 6–8 (PDF 35–37)

import Mathlib
import Definitions.Def_ShippingContracts_Model

open MeasureTheory ProbabilityTheory

namespace ShippingContracts

/-- **Theorem 8** (profit split under the flat rate), Song–Zhao, SSRN 3129499, p. 20 (PDF 20);
proof App. pp. 6–8 (PDF 35–37). Under `p > c > s`, `0 < u ≤ u'`, `c_u ≥ u'` and the demand law:
1. the flat rate `κ_C = (ν_C, 0, 0)` of Theorem 7 is feasible and coordinates the supply chain;
2. for every feasible flat-rate contract `κ` (`p_o = 0` or `p_u = 0`) that coordinates the
   supply chain, and all best responses `(r, q)` of the seller and `cap` of the shipper,
   the shipper's expected profit is `≥ 0`, and `> 0` iff `u < u'`; the seller's expected profit
   is `≥ 0`, and `> 0` iff `u < c_u`.

**Formalization Note.** "Can be greater than zero" is formalized as the exact sign conditions:
at `u = u'` the shipper's profit is `0`, and at `u = c_u` (which forces `u = u' = c_u`) both
profits are `0`. Clause 2 assumes `Coordinates P μ κ` rather than `ν = ν_C`. -/
theorem theorem_8 (P : Params) (hPr : P.Prices) (hSh : P.Shipping) (hSC : P.uE ≤ P.cu)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hD : DemandLaw μ) :
    (Feasible P ⟨nuC P, 0, 0⟩ ∧ Coordinates P μ ⟨nuC P, 0, 0⟩) ∧
    ∀ κ : Contract, Feasible P κ → (κ.po = 0 ∨ κ.pu = 0) → Coordinates P μ κ →
      ∀ r q cap : ℝ, SellerBR P μ κ r q → ShipperBR P μ κ r q cap →
        (0 ≤ shipperProfit P μ κ r q cap ∧
          (0 < shipperProfit P μ κ r q cap ↔ P.u < P.uE)) ∧
        (0 ≤ sellerProfit P μ κ r q ∧ (0 < sellerProfit P μ κ r q ↔ P.u < P.cu)) := by sorry

end ShippingContracts
