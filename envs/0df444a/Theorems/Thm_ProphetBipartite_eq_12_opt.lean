-- Prove2me | Theorems.Thm_ProphetBipartite_eq_12_opt
-- name    : ProphetBipartite.eq_12_opt
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:51:43.393027+00:00
-- url     : https://prove2.me/theorems/adf6f579-a864-4fc2-9f72-dbe595898ea9
-- title:
--   Display (12) — the prophet's expected value is $\mathbb 1_L^\top M\,\mathbb 1_R$
-- statement:
--   Let the edge values be independent with finite means and let $\mathrm{opt}$ be an optimal matching selector with matrix $M$ of (10). Then the prophet's expected value is
--
--   $$
--   \mathbb E_v\big[\mathrm{opt}(v)\big]=\mathbb 1_L^\top\cdot M\cdot\mathbb 1_R=\sum_{i\in L}\sum_{j\in R}M_{i,j}.
--   $$
--
--   This expresses the benchmark in the same matrix terms as the lower bound (11), so that the two can be compared.
--
--   Differences from the source:
--   - generalization: opt(v̂) is "a random optimal matching" with unspecified tie-breaking (p.6) → every opt with IsOptSelector (a maximum-value matching for each v, measurable level sets); reason: the paper fixes no tie-breaking rule; every concrete rule is an instance (a measurable one exists: first maximizer in a fixed enumeration)
--   - encoding: values drawn from distributions F_e on ℝ₊ (p.4), with M of (10) a real matrix → laws μ e on ℝ≥0 with ∫⁻ x ∂μ e ≠ ⊤ (finite means); reason: the paper's standing assumption: M (10) and opt = 1ᵀM1 (12) are real numbers only when the means are finite
--   - encoding: v ∼ F = ∏_e F_e, independent edge values (p.4) → the product measure Measure.pi μ on E → ℝ≥0; reason: Lean convention; same instances
--   - encoding: bipartite multi-graph G(L, R) with multi-edges E (p.4) → finite types L, R, E with endpoint maps left : E → L, right : E → R; M_ij, Q_ij aggregate the parallel edges from i to j; reason: Lean convention; parallel edges are distinct elements of E, and at most one lies in a matching
--   - encoding: expectations E_v[·] → real Bochner integrals ∫ … ∂(Measure.pi μ); reason: with finite means every integrand is integrable; same values
-- source:
--   Gravin, Wang, Prophet inequality for bipartite matching: merits of being simple and non adaptive, arXiv:1902.06243v1, display (12), p.8

import Mathlib
import Definitions.Def_ProphetBipartite_optValue
import Definitions.Def_ProphetBipartite_IsOptSelector
import Definitions.Def_ProphetBipartite_Mmat

open MeasureTheory
open scoped NNReal ENNReal

namespace ProphetBipartite

/-- **Display (12): the prophet's expected value is `𝟙_Lᵀ M 𝟙_R`.** Gravin & Wang,
arXiv:1902.06243v1, (12), p.8: "the expected value of the optimal matching opt achieved by the
prophet according to the definitions of matrix `M` and random variables `χ^{(i,j)}_opt(v̂)` (see
(10), (4)) is equal to `opt = 𝟙_Lᵀ · M · 𝟙_R`", i.e. `E_v[opt(v)] = ∑_{i,j} M_{i,j}`.

**Formalization Note.** Edge values are independent with laws `μ e` on `ℝ≥0` with finite means;
the identity holds for every measurable optimal matching selector `opt`. The expectation is a real
integral. -/
theorem eq_12_opt {L R E : Type*} [Fintype L] [Fintype R] [Fintype E]
    [DecidableEq L] [DecidableEq R] [DecidableEq E]
    (left : E → L) (right : E → R) (μ : E → Measure ℝ≥0) [∀ e, IsProbabilityMeasure (μ e)]
    (hμ : ∀ e, ∫⁻ x, (x : ℝ≥0∞) ∂(μ e) ≠ ⊤)
    (opt : (E → ℝ≥0) → Finset E) (hopt : IsOptSelector left right opt) :
    ∫ v, (optValue left right v : ℝ) ∂(Measure.pi μ) = ∑ i, ∑ j, Mmat left right opt μ i j := by sorry

end ProphetBipartite
