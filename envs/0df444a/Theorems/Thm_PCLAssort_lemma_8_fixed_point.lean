-- Prove2me | Theorems.Thm_PCLAssort_lemma_8_fixed_point
-- name    : PCLAssort.lemma_8_fixed_point
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:22:38.046342+00:00
-- url     : https://prove2.me/theorems/70e454ab-0c8e-441b-9484-e5de7d4d9d9b
-- title:
--   Lemma 8 — $g(\cdot)/v_0$ has a fixed point
-- statement:
--   For a PCL instance and the knapsack family with sizes $s_i\ge0$ and capacity $c\ge0$, there is $\hat z\ge 0$ with
--
--   $$
--   g(\hat z)=v_0\,\hat z,
--   $$
--
--   that is, a fixed point of $g(\cdot)/v_0$, as required by step 2 of the framework.
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
--   Ghuge, Kwon, Nagarajan, Sharma, Constrained Assortment Optimization Under the Paired Combinatorial Logit Model, Oper. Res. 70(2) (2022), Lemma 8, p.793 (PDF p.9)

import Mathlib
import Definitions.Def_PCLAssort_PCLInstance
import Definitions.Def_PCLAssort_gValue

namespace PCLAssort

/-- Lemma 8 (Ghuge, Kwon, Nagarajan, Sharma, Oper. Res. 70(2), 2022, p.793): there exists a fixed point for `g(·)/v_0`, i.e. a `ẑ ≥ 0` with
`g(ẑ) = v_0 ẑ` (step 2 of the framework, p.792).

**Formalization Note.** Sizes `s_i ≥ 0` and capacity `c ≥ 0` (the knapsack setting of §4). -/
theorem lemma_8_fixed_point {n : ℕ} (I : PCLInstance n) (s : Fin n → ℝ) (hs : ∀ i, 0 ≤ s i)
    (c : ℝ) (hc : 0 ≤ c) :
    ∃ zhat : ℝ, 0 ≤ zhat ∧ gValue I s c zhat = I.v0 * zhat := by sorry

end PCLAssort
