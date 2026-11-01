-- Prove2me | Theorems.Thm_ProphetBipartite_fact_3_2
-- name    : ProphetBipartite.fact_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:51:44.264984+00:00
-- url     : https://prove2.me/theorems/78de0d41-e03c-4185-ba4d-1c182f5bd6e6
-- title:
--   Fact 3.2 — row and column sums of $Q$ are at most 1
-- statement:
--   Let the edge values be independent and let $\mathrm{opt}$ be an optimal matching selector with matrix $Q_{i,j}=\Pr_v[(i,j)\in\mathrm{opt}(v)]$ of (10). Then, coordinatewise,
--
--   $$
--   \mathbb 1_L\succeq Q\cdot\mathbb 1_R\quad\text{and}\quad\mathbb 1_R^\top\succeq\mathbb 1_L^\top\cdot Q,
--   $$
--
--   that is, $\sum_{j\in R}Q_{i,j}\le1$ for every $i\in L$ and $\sum_{i\in L}Q_{i,j}\le1$ for every $j\in R$.
--
--   This holds because the optimal matching uses at most one edge at each vertex; it is the only property of $Q$ that the proofs of Theorems 3.1 and 3.2 use.
--
--   Differences from the source:
--   - generalization: opt(v̂) is "a random optimal matching" with unspecified tie-breaking (p.6) → every opt with IsOptSelector (a maximum-value matching for each v, measurable level sets); reason: the paper fixes no tie-breaking rule; every concrete rule is an instance (a measurable one exists: first maximizer in a fixed enumeration)
--   - encoding: v ∼ F = ∏_e F_e, independent edge values (p.4) → the product measure Measure.pi μ on E → ℝ≥0; reason: Lean convention; same instances
--   - encoding: bipartite multi-graph G(L, R) with multi-edges E (p.4) → finite types L, R, E with endpoint maps left : E → L, right : E → R; M_ij, Q_ij aggregate the parallel edges from i to j; reason: Lean convention; parallel edges are distinct elements of E, and at most one lies in a matching
--   - generalization: finite means (standing assumption) → not assumed; reason: Q is a matrix of probabilities, defined for every law; the source's case is included
-- source:
--   Gravin, Wang, Prophet inequality for bipartite matching: merits of being simple and non adaptive, arXiv:1902.06243v1, Fact 3.2, p.9

import Mathlib
import Definitions.Def_ProphetBipartite_IsOptSelector
import Definitions.Def_ProphetBipartite_Mmat

open MeasureTheory
open scoped NNReal

namespace ProphetBipartite

/-- **Fact 3.2: the row and column sums of `Q` are at most 1.** Gravin & Wang, arXiv:1902.06243v1,
p.9: "`𝟙_L ⪰ Q · 𝟙_R` and `𝟙_Rᵀ ⪰ 𝟙_Lᵀ · Q`, where `⪰` stands for coordinate-wise inequality `≥`",
i.e. `∑_j Q_{i,j} ≤ 1` for every `i ∈ L` and `∑_i Q_{i,j} ≤ 1` for every `j ∈ R`, where
`Q_{i,j} = Pr_v[(i, j) ∈ opt(v)]` (10).

**Formalization Note.** The values are independent with laws `μ e` on `ℝ≥0`; the fact holds for
every measurable optimal matching selector `opt`. No finiteness of means is needed. -/
theorem fact_3_2 {L R E : Type*} [Fintype L] [Fintype R] [Fintype E] [DecidableEq E]
    (left : E → L) (right : E → R) (μ : E → Measure ℝ≥0) [∀ e, IsProbabilityMeasure (μ e)]
    (opt : (E → ℝ≥0) → Finset E) (hopt : IsOptSelector left right opt) :
    (∀ i, ∑ j, Qmat left right opt μ i j ≤ 1) ∧ ∀ j, ∑ i, Qmat left right opt μ i j ≤ 1 := by sorry

end ProphetBipartite
