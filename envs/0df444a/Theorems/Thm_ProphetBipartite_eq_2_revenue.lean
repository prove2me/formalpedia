-- Prove2me | Theorems.Thm_ProphetBipartite_eq_2_revenue
-- name    : ProphetBipartite.eq_2_revenue
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T09:49:55.205276+00:00
-- url     : https://prove2.me/theorems/0c1c351a-42b1-48a9-9b1d-927728db7038
-- title:
--   Display (2) — the revenue of V-add equals the prices of the covered vertices
-- statement:
--   Let $\mathrm{V\text{-}add}(l,r)$ run along a sequence of edges $\sigma$ with prices $l\in\mathbb R_{\ge0}^L$, $r\in\mathbb R_{\ge0}^R$. For every value profile $v$, with $\mathcal A(v)$ the accepted edges and $X_L(v)$, $X_R(v)$ the covered vertices,
--
--   $$
--   \sum_{(i,j)\in\mathcal A(v)}(l_i+r_j)=\sum_{i\in X_L(v)}l_i+\sum_{j\in X_R(v)}r_j ,
--   $$
--
--   and consequently, for independent edge values $v\sim\prod_eF_e$,
--
--   $$
--   \mathbf{Rev}=\mathbb E_v\Big[\sum_{(i,j)\in\mathcal A(v)}(l_i+r_j)\Big]=\mathbb E_v\Big[\sum_{i\in X_L(v)}l_i+\sum_{j\in X_R(v)}r_j\Big].
--   $$
--
--   The revenue is the part of the policy's value paid as prices; this identity attributes it to the covered vertices instead of the accepted edges, which is the first half of the lower bound (8).
--
--   **Formalization Note** The expectations are `lintegral`s in $[0,\infty]$.
--
--   Differences from the source:
--   - generalization: the expectation identity (2) for the arrival order σ → the identity for every value profile v (pathwise) and in expectation, for every list σ of edges; reason: the expectation identity is the second conjunct and follows from the first; an arrival order is a list
--   - reading: V-add is described by "two positive real vectors" l, r (p.5) → prices l : L → ℝ≥0, r : R → ℝ≥0 (zero allowed); reason: the proof of Theorem 3.1 (p.9) finds "non negative price vectors" and Algorithm 1 may start at 0-vectors (p.10); a solution of (17) can have zero coordinates, so "positive" means nonnegative
--   - encoding: v ∼ F = ∏_e F_e, independent edge values (p.4) → the product measure Measure.pi μ on E → ℝ≥0; reason: Lean convention; same instances
--   - encoding: expectations E_v[·] → lintegral in ℝ≥0∞ of the ℝ≥0-valued sums; reason: nonnegative integrands; same values
-- source:
--   Gravin, Wang, Prophet inequality for bipartite matching: merits of being simple and non adaptive, arXiv:1902.06243v1, §3.1, display (2), p.5

import Mathlib
import Definitions.Def_ProphetBipartite_vaddRun

open MeasureTheory
open scoped NNReal ENNReal

namespace ProphetBipartite

/-- **Display (2): the revenue of `V-add(l, r)` is the price of the covered vertices.** Gravin &
Wang, arXiv:1902.06243v1, §3.1, (2), p.5:

`Rev = E_v[∑_{(i,j)∈𝒜(v)} (l_i + r_j)] = E_v[∑_{i∈X_L(v)} l_i + ∑_{j∈X_R(v)} r_j]`.

Stated pathwise (for every value profile `v`) and in expectation over `v ∼ ∏_e F_e`.

**Formalization Note.** The order `σ` is any list of edges; the identity is a property of the run
and does not need `σ` to enumerate `E`. Expectations are `lintegral`s in `ℝ≥0∞`. -/
theorem eq_2_revenue {L R E : Type*} [Fintype E] [DecidableEq L] [DecidableEq R] [DecidableEq E]
    (left : E → L) (right : E → R) (μ : E → Measure ℝ≥0) [∀ e, IsProbabilityMeasure (μ e)]
    (l : L → ℝ≥0) (r : R → ℝ≥0) (σ : List E) :
    (∀ v : E → ℝ≥0, ∑ e ∈ vaddAccepted left right l r σ v, (l (left e) + r (right e)) =
        ∑ i ∈ vaddCoveredL left right l r σ v, l i + ∑ j ∈ vaddCoveredR left right l r σ v, r j) ∧
      ∫⁻ v, ((∑ e ∈ vaddAccepted left right l r σ v, (l (left e) + r (right e)) : ℝ≥0) : ℝ≥0∞)
          ∂(Measure.pi μ) =
        ∫⁻ v, ((∑ i ∈ vaddCoveredL left right l r σ v, l i +
            ∑ j ∈ vaddCoveredR left right l r σ v, r j : ℝ≥0) : ℝ≥0∞) ∂(Measure.pi μ) := by sorry

end ProphetBipartite
