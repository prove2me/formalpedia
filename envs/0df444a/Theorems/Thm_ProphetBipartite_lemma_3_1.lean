-- Prove2me | Theorems.Thm_ProphetBipartite_lemma_3_1
-- name    : ProphetBipartite.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:51:52.661163+00:00
-- url     : https://prove2.me/theorems/2e6f2f1d-ef3f-42f2-833d-f4a39c23d4cc
-- title:
--   Lemma 3.1 — lower bound on the expected surplus of V-add
-- statement:
--   Let the edge values be independent, $v,\hat v\sim F=\prod_eF_e$ on $\mathbb R_+$ with finite means, let $\mathrm{opt}$ be an optimal matching selector, $\sigma$ an arrival order, and $l\in\mathbb R_{\ge0}^L$, $r\in\mathbb R_{\ge0}^R$. Let $\mathcal A(v)$, $X_L(v)$, $X_R(v)$ be the accepted edges and covered vertices of $\mathrm{V\text{-}add}(l,r)$, and define the expected surplus, display (3), by
--
--   $$
--   \mathbf{Surplus}=\mathbb E_v\Big[\sum_{e\in\mathcal A(v),\ e=(i,j)}\big[v_e-l_i-r_j\big]^+\Big].
--   $$
--
--   Then
--
--   $$
--   \mathbf{Surplus}\ \ge\ \mathbb E_v\Big[\sum_{i\notin X_L(v)}\ \sum_{j\notin X_R(v)}\Big[\mathbb E_{\hat v}\big[\chi^{(i,j)}_{\mathrm{opt}}(\hat v)\big]-(l_i+r_j)\Pr_{\hat v}\big[(i,j)\in\mathrm{opt}(\hat v)\big]\Big]^+\Big],
--   $$
--
--   where the inner expectation and probability are the entries $M_{i,j}$ and $Q_{i,j}$ of (10).
--
--   The surplus is the part of the policy's value above the prices; together with the revenue identity (2) this gives the lower bound (8).
--
--   Differences from the source:
--   - reading: V-add is described by "two positive real vectors" l, r (p.5) → prices l : L → ℝ≥0, r : R → ℝ≥0 (zero allowed); reason: the proof of Theorem 3.1 (p.9) finds "non negative price vectors" and Algorithm 1 may start at 0-vectors (p.10); a solution of (17) can have zero coordinates, so "positive" means nonnegative
--   - generalization: opt(v̂) is "a random optimal matching" with unspecified tie-breaking (p.6) → every opt with IsOptSelector (a maximum-value matching for each v, measurable level sets); reason: the paper fixes no tie-breaking rule; every concrete rule is an instance (a measurable one exists: first maximizer in a fixed enumeration)
--   - encoding: values drawn from distributions F_e on ℝ₊ (p.4), with M of (10) a real matrix → laws μ e on ℝ≥0 with ∫⁻ x ∂μ e ≠ ⊤ (finite means); reason: the paper's standing assumption: M (10) and opt = 1ᵀM1 (12) are real numbers only when the means are finite
--   - encoding: v ∼ F = ∏_e F_e, independent edge values (p.4) → the product measure Measure.pi μ on E → ℝ≥0; reason: Lean convention; same instances
--   - encoding: bipartite multi-graph G(L, R) with multi-edges E (p.4) → finite types L, R, E with endpoint maps left : E → L, right : E → R; M_ij, Q_ij aggregate the parallel edges from i to j; reason: Lean convention; parallel edges are distinct elements of E, and at most one lies in a matching
--   - encoding: expectations E_v[·] → real Bochner integrals ∫ … ∂(Measure.pi μ); reason: with finite means every integrand is integrable; same values
-- source:
--   Gravin, Wang, Prophet inequality for bipartite matching: merits of being simple and non adaptive, arXiv:1902.06243v1, Lemma 3.1 and display (5), p.6; Surplus display (3), p.6

import Mathlib
import Definitions.Def_ProphetBipartite_IsOrder
import Definitions.Def_ProphetBipartite_vaddRun
import Definitions.Def_ProphetBipartite_IsOptSelector
import Definitions.Def_ProphetBipartite_Mmat

open MeasureTheory
open scoped NNReal ENNReal

namespace ProphetBipartite

/-- **Lemma 3.1 (the expected surplus).** Gravin & Wang, arXiv:1902.06243v1, §3.1, p.6, with the
definition (3) of the surplus: for any prices `l, r ≥ 0` and any arrival order `σ`,

`Surplus = E_v[∑_{e∈𝒜(v)} [v_e − l_i − r_j]⁺] ≥ E_v[∑_{i∉X_L(v), j∉X_R(v)} [E_v̂[χ^{(i,j)}_opt(v̂)] − (l_i + r_j) Pr_v̂[(i,j) ∈ opt(v̂)]]⁺]`,

where `e = (i, j)` in the first sum, `𝒜(v)`, `X_L(v)`, `X_R(v)` are the accepted edges and the
covered vertices of `V-add(l, r)`, and `v, v̂ ∼ F = ∏_e F_e` independently. The inner expectations
are the entries `M_{i,j}`, `Q_{i,j}` of (10).

**Formalization Note.** The edge values are independent with laws `μ e` on `ℝ≥0` with finite means
(the paper's standing assumption; `M` is a real matrix). The statement holds for every measurable
optimal matching selector `opt`. Expectations are real (Bochner) integrals; with finite means both
integrands are integrable. -/
theorem lemma_3_1 {L R E : Type*} [Fintype L] [Fintype R] [Fintype E]
    [DecidableEq L] [DecidableEq R] [DecidableEq E]
    (left : E → L) (right : E → R) (μ : E → Measure ℝ≥0) [∀ e, IsProbabilityMeasure (μ e)]
    (hμ : ∀ e, ∫⁻ x, (x : ℝ≥0∞) ∂(μ e) ≠ ⊤)
    (opt : (E → ℝ≥0) → Finset E) (hopt : IsOptSelector left right opt)
    (l : L → ℝ≥0) (r : R → ℝ≥0) (σ : List E) (hσ : IsOrder σ) :
    ∫ v, ∑ i ∈ (vaddCoveredL left right l r σ v)ᶜ, ∑ j ∈ (vaddCoveredR left right l r σ v)ᶜ,
        max (Mmat left right opt μ i j - ((l i : ℝ) + r j) * Qmat left right opt μ i j) 0
        ∂(Measure.pi μ) ≤
      ∫ v, ∑ e ∈ vaddAccepted left right l r σ v,
        max ((v e : ℝ) - l (left e) - r (right e)) 0 ∂(Measure.pi μ) := by sorry

end ProphetBipartite
