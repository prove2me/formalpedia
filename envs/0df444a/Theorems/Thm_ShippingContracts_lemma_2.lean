-- Prove2me | Theorems.Thm_ShippingContracts_lemma_2
-- name    : ShippingContracts.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:54:09.16966+00:00
-- url     : https://prove2.me/theorems/48618644-ea7d-47aa-a866-7ca150bd18b1
-- title:
--   Lemma 2 — $H(c,q)$ is jointly convex on $\{c\le q\}$ and on $\{c>q\}$, and increasing in $c$ on $\{c>q\}$ (corrected: monotone in $c$ only)
-- statement:
--   Throughout, $p>c>s$ are the selling price, procurement cost and salvage value, $c_o=c-s$ and $c_u=p-c$ the seller's overage and underage costs, $0<u\le u'$ the unit costs of regular and emergency shipping capacity, and $D\ge0$ the demand, with finite mean and a c.d.f. $F$ that is continuous and strictly increasing on $\{x\ge0: F(x)<1\}$. $S=\min(q,D)$ is the shipment and $x^+=\max(x,0)$.
--
--   Assume moreover the standing assumption of Section 5, $c_u\ge u'$. Let $H(c,q)=E[c_o(q-D)^++c_u(D-q)^+]+uc+u'E[(\min(q,D)-c)^+]$ be the supply chain's total cost (5.8). Then:
--
--   1. $H$ is jointly convex in $(c,q)$ on the region $\{(c,q): c\le q\}$;
--   2. $H$ is jointly convex in $(c,q)$ on the region $\{(c,q): c>q\}$;
--   3. for every $q$, the map $c\mapsto H(c,q)$ is strictly increasing on $\{c>q\}$.
--
--   Splitting the plane along $c=q$ makes the cost convex on each side, which is what allows the first best (Theorem 4) to be found by minimizing out $c$ and gluing two convex one-dimensional problems.
--
--   **Formalization Note** $H$ is `totalCost P μ cap q`, capacity first.
--
--   Differences from the source:
--   - reading: D with density f and c.d.f. F, both continuous and differentiable; F⁻¹ used as an inverse with F⁻¹(0) = 0, integrals from 0 (p. 9; App. p. 3) → μ a probability measure with D ≥ 0 a.s., finite mean, F = cdf μ continuous and strictly increasing on {x ≥ 0 : F(x) < 1}; reason: these are the properties the paper's use of F⁻¹ on [0, 1), of integrals from 0 and of E[D] in the objectives requires; F(0) = 0 follows.
--   - generalization: a density f of D exists → no density assumed; reason: every law with a density and a c.d.f. strictly increasing on its support from 0 is an instance, so the statement specializes to the paper's.
--   - reading: u > 0 not stated in the theorem (it is used in the proofs, "= u > 0", App. p. 2) → 0 < u as a hypothesis; reason: without it the fractile (u' − u)/u' is undefined at u' = 0 and the shipper's cost need not increase beyond q.
--   - correction: H(c, q) is a monotonically increasing function in c and q for c > q → strictly increasing in c on {c > q}; nothing about q; reason: false in q: on {c > q} the cost is E[c_o(q − D)⁺ + c_u(D − q)⁺] + uc, whose q-derivative (c_o + c_u)F(q) − c_u is negative for small q; with D ~ Uniform(0,1), c_o = 1, c_u = 2, u = 1/2, u' = 1, c = 1: H(1, 0) = 3/2 > 7/8 = H(1, 1/2), and these parameters satisfy all assumptions (p = 3, c = 1, s = 0). The proof of Theorem 4 uses only monotonicity in c.
--   - generalization: monotonically increasing in c → strictly increasing in c (StrictMonoOn); reason: strict monotonicity implies monotonicity, so the statement specializes.
--   - generalization: the regions c ≤ q and c > q of the decision domain c, q ≥ 0 → the regions {c ≤ q} and {c > q} of all real (c, q); reason: the printed regions carry no sign restriction; restricting to c, q ≥ 0 gives the paper's claims.
-- source:
--   Song–Zhao, Supply Chain Coordination for E-Commerce: Risk Penalty vs. Flat Rate (SSRN manuscript 3129499, titled 'Supply Chain Integration for Online Shopping Holidays: Risk Penalty vs. Flat Rate'; version of record MSOM 2021, doi:10.1287/msom.2021.1008), Lemma 2, p. 17 (PDF 17); proof App. pp. 3–4 (PDF 32–33)

import Mathlib
import Definitions.Def_ShippingContracts_Model

open MeasureTheory ProbabilityTheory

namespace ShippingContracts

/-- **Lemma 2** (convexity and monotonicity of `H(c, q)`), Song–Zhao, SSRN 3129499, p. 17 (PDF 17);
proof App. pp. 3–4 (PDF 32–33). Under `p > c > s`, `0 < u ≤ u'`, the §5 assumption `c_u ≥ u'`
(p. 17) and the demand law:
1. `H(c, q)` is jointly convex in `(c, q)` on `{c ≤ q}`;
2. `H(c, q)` is jointly convex in `(c, q)` on `{c > q}`;
3. for every `q`, `H(·, q)` is strictly increasing on `{c > q}`.

**Formalization Note.** Corrected: the printed third bullet also claims monotonicity in `q` on
`{c > q}`, which is false (e.g. `D ~ U(0,1)`, `c_o = 1`, `c_u = 2`, `u = 1/2`, `u' = 1`:
`H(1, 0) = 3/2 > 7/8 = H(1, 1/2)`). `H` is `totalCost P μ cap q`, capacity first. The regions are
the printed ones, over all real `(c, q)`; monotonicity is strict (`u > 0`). -/
theorem lemma_2 (P : Params) (hPr : P.Prices) (hSh : P.Shipping) (hSC : P.uE ≤ P.cu)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hD : DemandLaw μ) :
    ConvexOn ℝ {x : ℝ × ℝ | x.1 ≤ x.2} (fun x => totalCost P μ x.1 x.2) ∧
    ConvexOn ℝ {x : ℝ × ℝ | x.2 < x.1} (fun x => totalCost P μ x.1 x.2) ∧
    ∀ q : ℝ, StrictMonoOn (fun cap => totalCost P μ cap q) (Set.Ioi q) := by sorry

end ShippingContracts
