-- Prove2me | Theorems.Thm_PCLAssort_lemma_2_edge_sign
-- name    : PCLAssort.lemma_2_edge_sign
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:20:59.493183+00:00
-- url     : https://prove2.me/theorems/32854e1d-b1a8-4f55-a688-271c566a53f9
-- title:
--   Lemma 2 — sign structure of the edges of $G_z$ (corrected: negative → nonpositive)
-- statement:
--   Consider a PCL instance, $z\in\mathbb R$ and the reduction graph $G_z$, and write $\bar r_i=r_i-z$. For every product $i$:
--
--   1. if $\bar r_i<0$, then every edge leaving vertex $i$ in $G_z$ has a nonpositive weight;
--   2. if $\bar r_i\ge 0$, then every edge leaving vertex $i$ in $G_z$ has a nonnegative weight.
--
--   So $\tilde G_z$ contains every edge leaving the vertices with $r_i\ge z$, and vertices with $r_i<z$ never gain from being selected.
--
--   Differences from the source:
--   - correction: if r̄_i < 0, every edge leaving i has a negative weight → if r̄_i < 0, every edge leaving i has a nonpositive weight; reason: false as printed: n = 2, v = (0, 0.7), r = (0, 0.5), γ ≡ 0.5, z = 1 gives r̄_1 = −1 and both edges leaving vertex 1 of weight 0 (and v = (0.4, 0.7), γ ≡ 1 gives w_12 = 0)
--   - reading: v₀ is the no-purchase weight, with no sign stated (p.789) → v₀ > 0 (field of PCLInstance); reason: the paper divides by v₀ (fixed point of g(·)/v₀, p.792); with v₀ = 0 the framework degenerates
--   - encoding: γ_ij ∈ [0, 1] (p.789) → γ_ij ∈ (0, 1] for i ≠ j; reason: v_i^{1/γ_ij} is undefined at γ_ij = 0; this excludes only the undefined case
--   - encoding: vertices [n+1] with dummy n+1, products [n] → Option (Fin n) with none the dummy, Fin n; reason: relabelling; same graph
--   - reading: edge weights (4)–(6), whose ξ⁻/ψ⁻ subscripts disagree with the prose on pp.790–791 → closed forms: the pair (i,j) puts r̄_i a/D on (i,n+1), r̄_j b/D on (j,n+1), v_i r̄_i − r̄_i a/D on (i,j), v_j r̄_j − r̄_j b/D on (j,i); reason: the closed forms are unambiguous and make Lemma 1 hold; the subscripts are a typesetting inconsistency
-- source:
--   Ghuge, Kwon, Nagarajan, Sharma, Constrained Assortment Optimization Under the Paired Combinatorial Logit Model, Oper. Res. 70(2) (2022), Lemma 2, p.791 (PDF p.7)

import Mathlib
import Definitions.Def_PCLAssort_PCLInstance
import Definitions.Def_PCLAssort_pclEdges
import Definitions.Def_PCLAssort_pclWeight

namespace PCLAssort

/-- Lemma 2 (Ghuge, Kwon, Nagarajan, Sharma, Oper. Res. 70(2), 2022, p.791), corrected: if `r̄_i < 0` (respectively `r̄_i ≥ 0`) for a vertex `i`, then
every edge leaving vertex `i` in `G_z` has a nonpositive (resp. nonnegative) weight; `r̄_i = r_i − z`.

**Formalization Note.** The page says "negative" in the first clause. That is false: for `n = 2`,
`v = (0, 0.7)`, `r = (0, 0.5)`, `γ ≡ 0.5`, `z = 1` one has `r̄_1 = −1 < 0` but both edges leaving
vertex 1 have weight `0`. The first clause is corrected to "nonpositive"; the second clause is as
printed. -/
theorem lemma_2_edge_sign {n : ℕ} (I : PCLInstance n) (z : ℝ) (i : Fin n) :
    (I.r i - z < 0 → ∀ e ∈ pclEdges n, e.1 = some i → pclWeight I z e ≤ 0) ∧
    (0 ≤ I.r i - z → ∀ e ∈ pclEdges n, e.1 = some i → 0 ≤ pclWeight I z e) := by sorry

end PCLAssort
