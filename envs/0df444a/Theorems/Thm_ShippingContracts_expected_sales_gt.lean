-- Prove2me | Theorems.Thm_ShippingContracts_expected_sales_gt
-- name    : ShippingContracts.expected_sales_gt
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T07:54:26.099605+00:00
-- url     : https://prove2.me/theorems/ba0a95e7-3dd0-4939-86ee-5c009d3d46fe
-- title:
--   Proof of Theorem 8 — $E[\min(x,D)]=x-\int_0^xF$ and $x(1-F(x))<E[\min(x,D)]$ for $x>0$
-- statement:
--   Let the demand $D\ge0$ have finite mean and a c.d.f. $F$ continuous and strictly increasing on $\{x\ge0:F(x)<1\}$. Then for every $x>0$,
--   $$E[\min(x,D)]=x-\int_0^xF(t)\,dt\qquad\text{and}\qquad x\,\big(1-F(x)\big)<E[\min(x,D)].$$
--
--   This is the step behind both claims of Theorem 8: with $x=c^0$ or $x=q^*_F$, the expected sales exceed the level that makes the shipper's and the seller's profits vanish.
--
--   **Formalization Note** The paper reaches these by integration by parts against the density; the statement uses only the c.d.f.
--
--   Differences from the source:
--   - reading: D with density f and c.d.f. F, both continuous and differentiable; F⁻¹ used as an inverse with F⁻¹(0) = 0, integrals from 0 (p. 9; App. p. 3) → μ a probability measure with D ≥ 0 a.s., finite mean, F = cdf μ continuous and strictly increasing on {x ≥ 0 : F(x) < 1}; reason: these are the properties the paper's use of F⁻¹ on [0, 1), of integrals from 0 and of E[D] in the objectives requires; F(0) = 0 follows.
--   - generalization: a density f of D exists → no density assumed; reason: every law with a density and a c.d.f. strictly increasing on its support from 0 is an instance, so the statement specializes to the paper's.
--   - encoding: u'(D − c⁰)F(D)|₀^{c⁰} − u'∫₀^{c⁰}F(D)dD + (u' − u)c⁰ > −u'c⁰F(c⁰) + (u' − u)c⁰, i.e. ∫₀ˣF < xF(x) → E[min(x, D)] = x − ∫₀ˣ F and x(1 − F(x)) < E[min(x, D)]; reason: the two forms are equivalent by the first identity.
--   - generalization: x = c⁰ (and x = q*_F on App. pp. 7–8) in the model with its cost parameters → every x > 0, no cost parameters; reason: c⁰ and q*_F are positive points of this kind in the cases where the proof applies the step, so the statement specializes.
-- source:
--   Song–Zhao, Supply Chain Coordination for E-Commerce: Risk Penalty vs. Flat Rate (SSRN manuscript 3129499, titled 'Supply Chain Integration for Online Shopping Holidays: Risk Penalty vs. Flat Rate'; version of record MSOM 2021, doi:10.1287/msom.2021.1008), proof of Theorem 8, App. p. 6 (PDF 35), and the analogous steps on App. pp. 7–8 (PDF 36–37)

import Mathlib
import Definitions.Def_ShippingContracts_Model

open MeasureTheory ProbabilityTheory

namespace ShippingContracts

/-- **The strict step of the proof of Theorem 8**, Song–Zhao, SSRN 3129499, App. p. 6 (PDF 35)
(and App. pp. 7–8, PDF 36–37): under the demand law, for every `x > 0`,
`E[min(x, D)] = x − ∫₀ˣ F(t) dt` and `x (1 − F(x)) < E[min(x, D)]`.

**Formalization Note.** The paper obtains these by integration by parts against the density;
the statement uses only `F = cdf μ`. -/
theorem expected_sales_gt (μ : Measure ℝ) [IsProbabilityMeasure μ] (hD : DemandLaw μ)
    (x : ℝ) (hx : 0 < x) :
    ∫ d, min x d ∂μ = x - ∫ t in (0 : ℝ)..x, cdf μ t ∧
    x * (1 - cdf μ x) < ∫ d, min x d ∂μ := by sorry

end ShippingContracts
