-- Prove2me | Theorems.Thm_PCLAssort_lemma_9_dual_fixed_point
-- name    : PCLAssort.lemma_9_dual_fixed_point
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:22:16.263837+00:00
-- url     : https://prove2.me/theorems/ff66695c-ba98-4890-9836-39b6477f0a4a
-- title:
--   Lemma 9 — an optimal solution of (D) gives the fixed point
-- statement:
--   For a PCL instance and the knapsack family with sizes $s_i\ge0$ and capacity $c\ge0$, if $(\hat\alpha,\hat\beta,\hat\gamma,\hat\delta,\hat z)$ is an optimal solution of the LP (D), then
--
--   $$
--   g(\hat z)=v_0\,\hat z,
--   $$
--
--   that is, $\hat z$ is the fixed point of $g(\cdot)/v_0$. One LP solve therefore replaces a search for the fixed point.
--
--   Differences from the source:
--   - reading: sizes s_i and capacity c of the knapsack family of §4, no sign stated → 0 ≤ s_i and 0 ≤ c; reason: sizes and limits are nonnegative in the paper's model; then LP(z) is feasible and g(z) is a finite maximum
--   - encoding: g(z) = maximum of LP(z) → sSup of the objective values over the feasible set; reason: with 0 ≤ s, 0 ≤ c the feasible set is a nonempty polytope, so the supremum is the attained maximum
--   - encoding: dual variable γ_i → field γd; reason: renaming to avoid the clash with γ_ij
--   - encoding: α_ij, β_ij for (i,j) ∈ E → α, β indexed by all ordered pairs of vertices; reason: only the values on E occur in (D); the others are unconstrained and irrelevant
--   - reading: v₀ is the no-purchase weight, with no sign stated (p.789) → v₀ > 0 (field of PCLInstance); reason: the paper divides by v₀ (fixed point of g(·)/v₀, p.792); with v₀ = 0 the framework degenerates
--   - encoding: γ_ij ∈ [0, 1] (p.789) → γ_ij ∈ (0, 1] for i ≠ j; reason: v_i^{1/γ_ij} is undefined at γ_ij = 0; this excludes only the undefined case
--   - encoding: vertices [n+1] with dummy n+1, products [n] → Option (Fin n) with none the dummy, Fin n; reason: relabelling; same graph
--   - reading: edge weights (4)–(6), whose ξ⁻/ψ⁻ subscripts disagree with the prose on pp.790–791 → closed forms: the pair (i,j) puts r̄_i a/D on (i,n+1), r̄_j b/D on (j,n+1), v_i r̄_i − r̄_i a/D on (i,j), v_j r̄_j − r̄_j b/D on (j,i); reason: the closed forms are unambiguous and make Lemma 1 hold; the subscripts are a typesetting inconsistency
--   - encoding: y ∈ ℝ^E → y : V × V → ℝ with y = 0 off E; reason: a linear copy of the same polytope; feasibility, objective and extreme points correspond
-- source:
--   Ghuge, Kwon, Nagarajan, Sharma, Constrained Assortment Optimization Under the Paired Combinatorial Logit Model, Oper. Res. 70(2) (2022), Lemma 9, p.793 (PDF p.9)

import Mathlib
import Definitions.Def_PCLAssort_PCLInstance
import Definitions.Def_PCLAssort_gValue
import Definitions.Def_PCLAssort_DualVars
import Definitions.Def_PCLAssort_dualObjective
import Definitions.Def_PCLAssort_DFeasible

namespace PCLAssort

/-- Lemma 9 (Ghuge, Kwon, Nagarajan, Sharma, Oper. Res. 70(2), 2022, p.793): if `(α̂, β̂, γ̂, δ̂, ẑ)` is an optimal solution to (D), then
`g(ẑ) = v_0 ẑ`, that is, `ẑ` is the fixed point of `g(·)/v_0`.

**Formalization Note.** (D) is a minimization; "optimal" is feasibility plus objective at most that
of every feasible point. The dual variable `γ_i` is the field `γd`. Sizes `s_i ≥ 0`, capacity
`c ≥ 0`. -/
theorem lemma_9_dual_fixed_point {n : ℕ} (I : PCLInstance n) (s : Fin n → ℝ) (hs : ∀ i, 0 ≤ s i)
    (c : ℝ) (hc : 0 ≤ c) (d : DualVars n) (hd : d ∈ DFeasible I s c)
    (hopt : ∀ d' ∈ DFeasible I s c, dualObjective c d ≤ dualObjective c d') :
    gValue I s c d.z = I.v0 * d.z := by sorry

end PCLAssort
