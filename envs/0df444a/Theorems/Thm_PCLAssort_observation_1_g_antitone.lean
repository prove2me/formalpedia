-- Prove2me | Theorems.Thm_PCLAssort_observation_1_g_antitone
-- name    : PCLAssort.observation_1_g_antitone
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:22:05.666918+00:00
-- url     : https://prove2.me/theorems/4faec6f9-b033-4f3d-b772-9bccb5f0067d
-- title:
--   Observation 1 — $g(z)$ is nonincreasing
-- statement:
--   For a PCL instance and the knapsack family with sizes $s_i\ge0$ and capacity $c\ge0$, the optimal value $g(z)$ of LP$(z)$ is a nonincreasing function of $z\in\mathbb R$.
--
--   The edge weights $w_{ij}(z)$ depend on $z$ through $\bar r_i=r_i-z$ with nonnegative coefficients, which is what makes the fixed point of $g(\cdot)/v_0$ well defined.
--
--   Differences from the source:
--   - reading: sizes s_i and capacity c of the knapsack family of §4, no sign stated → 0 ≤ s_i and 0 ≤ c; reason: sizes and limits are nonnegative in the paper's model; then LP(z) is feasible and g(z) is a finite maximum
--   - encoding: g(z) = maximum of LP(z) → sSup of the objective values over the feasible set; reason: with 0 ≤ s, 0 ≤ c the feasible set is a nonempty polytope, so the supremum is the attained maximum
--   - reading: v₀ is the no-purchase weight, with no sign stated (p.789) → v₀ > 0 (field of PCLInstance); reason: the paper divides by v₀ (fixed point of g(·)/v₀, p.792); with v₀ = 0 the framework degenerates
--   - encoding: γ_ij ∈ [0, 1] (p.789) → γ_ij ∈ (0, 1] for i ≠ j; reason: v_i^{1/γ_ij} is undefined at γ_ij = 0; this excludes only the undefined case
--   - encoding: vertices [n+1] with dummy n+1, products [n] → Option (Fin n) with none the dummy, Fin n; reason: relabelling; same graph
--   - reading: edge weights (4)–(6), whose ξ⁻/ψ⁻ subscripts disagree with the prose on pp.790–791 → closed forms: the pair (i,j) puts r̄_i a/D on (i,n+1), r̄_j b/D on (j,n+1), v_i r̄_i − r̄_i a/D on (i,j), v_j r̄_j − r̄_j b/D on (j,i); reason: the closed forms are unambiguous and make Lemma 1 hold; the subscripts are a typesetting inconsistency
--   - encoding: y ∈ ℝ^E → y : V × V → ℝ with y = 0 off E; reason: a linear copy of the same polytope; feasibility, objective and extreme points correspond
-- source:
--   Ghuge, Kwon, Nagarajan, Sharma, Constrained Assortment Optimization Under the Paired Combinatorial Logit Model, Oper. Res. 70(2) (2022), Observation 1, p.793 (PDF p.9)

import Mathlib
import Definitions.Def_PCLAssort_PCLInstance
import Definitions.Def_PCLAssort_gValue

namespace PCLAssort

/-- Observation 1 (Ghuge, Kwon, Nagarajan, Sharma, Oper. Res. 70(2), 2022, p.793): the function `g(z)`, the optimal value of LP(z), is nonincreasing
in `z`.

**Formalization Note.** Sizes `s_i ≥ 0` and capacity `c ≥ 0` (the knapsack setting of §4); then
LP(z) is feasible and bounded and `g(z)` is its maximum. -/
theorem observation_1_g_antitone {n : ℕ} (I : PCLInstance n) (s : Fin n → ℝ) (hs : ∀ i, 0 ≤ s i)
    (c : ℝ) (hc : 0 ≤ c) :
    Antitone (fun z => gValue I s c z) := by sorry

end PCLAssort
