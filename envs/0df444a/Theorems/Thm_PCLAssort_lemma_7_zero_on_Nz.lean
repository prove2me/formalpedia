-- Prove2me | Theorems.Thm_PCLAssort_lemma_7_zero_on_Nz
-- name    : PCLAssort.lemma_7_zero_on_Nz
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:22:32.329661+00:00
-- url     : https://prove2.me/theorems/0ef88348-3532-4cc4-afcc-1eb66c31ab70
-- title:
--   Lemma 7 — an optimal LP$(z)$ solution vanishing on $N_z$
-- statement:
--   Consider LP$(z)$ for the knapsack family with sizes $s_i\ge 0$ and capacity $c$, and let $N_z=\{i\in[n]: r_i-z<0\}$ and $P_z=V\setminus N_z$ (which contains the dummy vertex). Given an optimal solution $(x^*,y^*)$ of LP$(z)$, there is another optimal solution $(\bar x,\bar y)$ with
--
--   $$
--   \bar x_i=0\ \ (i\in N_z),\qquad \bar x_i=x^*_i\ \ (i\in P_z).
--   $$
--
--   So no vertex with outgoing edges of negative weight contributes to the LP solution, and negative edges can be deleted, leaving $\tilde G_z$.
--
--   Differences from the source:
--   - reading: sizes s_i of the knapsack family of §4, no sign stated → 0 ≤ s_i; reason: sizes are nonnegative in the paper's model
--   - reading: v₀ is the no-purchase weight, with no sign stated (p.789) → v₀ > 0 (field of PCLInstance); reason: the paper divides by v₀ (fixed point of g(·)/v₀, p.792); with v₀ = 0 the framework degenerates
--   - encoding: γ_ij ∈ [0, 1] (p.789) → γ_ij ∈ (0, 1] for i ≠ j; reason: v_i^{1/γ_ij} is undefined at γ_ij = 0; this excludes only the undefined case
--   - encoding: vertices [n+1] with dummy n+1, products [n] → Option (Fin n) with none the dummy, Fin n; reason: relabelling; same graph
--   - reading: edge weights (4)–(6), whose ξ⁻/ψ⁻ subscripts disagree with the prose on pp.790–791 → closed forms: the pair (i,j) puts r̄_i a/D on (i,n+1), r̄_j b/D on (j,n+1), v_i r̄_i − r̄_i a/D on (i,j), v_j r̄_j − r̄_j b/D on (j,i); reason: the closed forms are unambiguous and make Lemma 1 hold; the subscripts are a typesetting inconsistency
--   - encoding: y ∈ ℝ^E → y : V × V → ℝ with y = 0 off E; reason: a linear copy of the same polytope; feasibility, objective and extreme points correspond
-- source:
--   Ghuge, Kwon, Nagarajan, Sharma, Constrained Assortment Optimization Under the Paired Combinatorial Logit Model, Oper. Res. 70(2) (2022), Lemma 7, p.793 (PDF p.9)

import Mathlib
import Definitions.Def_PCLAssort_PCLInstance
import Definitions.Def_PCLAssort_IsLPzOptimal

namespace PCLAssort

/-- Lemma 7 (Ghuge, Kwon, Nagarajan, Sharma, Oper. Res. 70(2), 2022, p.793): given an optimal solution `(x*, y*)` to LP(z), we can construct another
optimal solution `(x̄, ȳ)` such that `x̄_i = 0` for all `i ∈ N_z = {i ∈ [n] | r̄_i < 0}`, and
`x̄_i = x*_i` for all `i ∈ P_z = V ∖ N_z`.

**Formalization Note.** LP(z) is for the knapsack family of §4 with sizes `s_i ≥ 0` (the page's
"size of product i"); `c` is any real. `P_z` contains the dummy vertex `none`. -/
theorem lemma_7_zero_on_Nz {n : ℕ} (I : PCLInstance n) (s : Fin n → ℝ) (hs : ∀ i, 0 ≤ s i)
    (c z : ℝ) (p : (Option (Fin n) → ℝ) × (Option (Fin n) × Option (Fin n) → ℝ))
    (hp : IsLPzOptimal I s c z p) :
    ∃ q : (Option (Fin n) → ℝ) × (Option (Fin n) × Option (Fin n) → ℝ),
      IsLPzOptimal I s c z q ∧ (∀ i : Fin n, I.r i - z < 0 → q.1 (some i) = 0) ∧
        (∀ i : Fin n, 0 ≤ I.r i - z → q.1 (some i) = p.1 (some i)) ∧ q.1 none = p.1 none := by sorry

end PCLAssort
