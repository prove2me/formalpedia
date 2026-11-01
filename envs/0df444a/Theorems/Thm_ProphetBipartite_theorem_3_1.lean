-- Prove2me | Theorems.Thm_ProphetBipartite_theorem_3_1
-- name    : ProphetBipartite.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:51:06.728614+00:00
-- url     : https://prove2.me/theorems/3667cc06-36ac-4590-b94c-ce3215d4db15
-- title:
--   Theorem 3.1 — static vertex prices earn one third of the prophet's expected matching value
-- statement:
--   Let $G(L,R)$ be a finite bipartite multigraph with edge set $E$, and let the edge values be independent, $v_e\sim F_e$ on $\mathbb R_+$, each with finite mean. Then there are vertex prices $l\in\mathbb R_{\ge0}^L$ and $r\in\mathbb R_{\ge0}^R$ such that for **every** arrival order $\sigma$ of the edges,
--
--   $$
--   3\cdot\mathbb E_{v}\big[\mathrm{V\text{-}add}(l,r)\big]\ \ge\ \mathbb E_{v}\big[\mathrm{opt}(v)\big],
--   $$
--
--   where $\mathrm{V\text{-}add}(l,r)$ is the total value of the edges accepted by the vertex-additive policy with prices $l,r$ along $\sigma$, and $\mathrm{opt}(v)$ is the maximum value of a matching.
--
--   The prices depend only on the graph and the value distributions, never on the order: a single static, non-adaptive policy is a 3-approximation to the prophet for every arrival order.
--
--   **Formalization Note** Expectations are `lintegral`s in $[0,\infty]$ under the product law; finite means is the hypothesis $\int x\,d\mu_e<\infty$. Empty vertex or edge sets are allowed.
--
--   Differences from the source:
--   - reading: "There are vertex prices l, r such that V-add(l, r) ≥ opt/3", order left implicit → ∃ l r, ∀ σ (IsOrder σ): one price vector for every arrival order; reason: §3.1 fixes an order "unknown to us" (p.5) and the prices solve (16), which depends only on M and Q, not on σ; this is the stronger of the two readings
--   - reading: V-add is described by "two positive real vectors" l, r (p.5) → prices l : L → ℝ≥0, r : R → ℝ≥0 (zero allowed); reason: the proof of Theorem 3.1 (p.9) finds "non negative price vectors" and Algorithm 1 may start at 0-vectors (p.10); a solution of (17) can have zero coordinates, so "positive" means nonnegative
--   - encoding: values drawn from distributions F_e on ℝ₊ (p.4), with M of (10) a real matrix → laws μ e on ℝ≥0 with ∫⁻ x ∂μ e ≠ ⊤ (finite means); reason: the paper's standing assumption: M (10) and opt = 1ᵀM1 (12) are real numbers only when the means are finite
--   - encoding: v ∼ F = ∏_e F_e, independent edge values (p.4) → the product measure Measure.pi μ on E → ℝ≥0; reason: Lean convention; same instances
--   - encoding: bipartite multi-graph G(L, R) with multi-edges E (p.4) → finite types L, R, E with endpoint maps left : E → L, right : E → R; M_ij, Q_ij aggregate the parallel edges from i to j; reason: Lean convention; parallel edges are distinct elements of E, and at most one lies in a matching
--   - encoding: the adversary may choose an arrival order or a distribution over orders (p.5) → every fixed order σ, a duplicate-free list containing every edge; reason: a distribution over orders is covered by averaging the fixed-order bound
--   - encoding: ρ · E[Σ v_e] ≥ E[opt(v)] with ρ = 3 (p.5) → ∫⁻ optValue ≤ 3 * ∫⁻ vaddValue in ℝ≥0∞; reason: nonnegative integrands; same values; the constant multiplies, no division
-- source:
--   Gravin, Wang, Prophet inequality for bipartite matching: merits of being simple and non adaptive, arXiv:1902.06243v1, Theorem 3.1, p.9; model §2 p.4; prophet inequality p.5

import Mathlib
import Definitions.Def_ProphetBipartite_optValue
import Definitions.Def_ProphetBipartite_IsOrder
import Definitions.Def_ProphetBipartite_vaddRun

open MeasureTheory
open scoped NNReal ENNReal

namespace ProphetBipartite

/-- **Theorem 3.1 (static vertex prices are a 3-approximation of the prophet).** Gravin & Wang,
*Prophet inequality for bipartite matching: merits of being simple and non adaptive*,
arXiv:1902.06243v1, Theorem 3.1, p.9: "There are vertex prices `l, r` such that vertex-additive
policy `V-add(l, r) ≥ opt/3`."

Let `G(L, R)` be a finite bipartite multigraph with edge set `E`, and let the edge values be
independent, `v_e ∼ F_e` on `ℝ₊` with finite means. Then there are prices `l : L → ℝ≥0`,
`r : R → ℝ≥0` such that for **every** arrival order `σ` of the edges,

`E_v[opt(v)] ≤ 3 · E_v[V-add(l, r)]`.

**Formalization Note.** The prices are chosen before the order (`∃ l r, ∀ σ`): they depend only on
the graph and the value distributions. `opt(v)` is the maximum value of a matching (`optValue`),
`V-add(l, r)` the total value of the edges the policy accepts (`vaddValue`, ties accepted).
Expectations are `lintegral`s in `ℝ≥0∞` under the product law `Measure.pi μ`; finite means is the
hypothesis `∫⁻ x ∂(μ e) ≠ ⊤`. Empty `L`, `R`, `E` are allowed. -/
theorem theorem_3_1 {L R E : Type*} [Fintype L] [Fintype R] [Fintype E]
    [DecidableEq L] [DecidableEq R] [DecidableEq E]
    (left : E → L) (right : E → R) (μ : E → Measure ℝ≥0) [∀ e, IsProbabilityMeasure (μ e)]
    (hμ : ∀ e, ∫⁻ x, (x : ℝ≥0∞) ∂(μ e) ≠ ⊤) :
    ∃ (l : L → ℝ≥0) (r : R → ℝ≥0), ∀ σ : List E, IsOrder σ →
      ∫⁻ v, (optValue left right v : ℝ≥0∞) ∂(Measure.pi μ) ≤
        3 * ∫⁻ v, (vaddValue left right l r σ v : ℝ≥0∞) ∂(Measure.pi μ) := by sorry

end ProphetBipartite
