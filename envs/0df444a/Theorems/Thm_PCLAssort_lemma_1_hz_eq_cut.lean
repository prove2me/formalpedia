-- Prove2me | Theorems.Thm_PCLAssort_lemma_1_hz_eq_cut
-- name    : PCLAssort.lemma_1_hz_eq_cut
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:22:14.214034+00:00
-- url     : https://prove2.me/theorems/a1e0e88d-8320-4f9a-b0c8-a178dc1138c1
-- title:
--   Lemma 1 — $h_z(\mathbf 1_S)$ is the cut value of $S$ in $G_z$
-- statement:
--   Consider a PCL instance, a number $z\in\mathbb R$ and the reduction graph $G_z$ on the vertices $[n+1]$ with edge weights $w_{ij}(z)$. For any subset $S\subseteq[n]$,
--
--   $$
--   h_z(\mathbf 1_S)=\sum_{(i,j)\in E:\ i\in S,\ j\notin S}w_{ij}(z),
--   $$
--
--   where $\mathbf 1_S\in\{0,1\}^n$ is the indicator vector of $S$.
--
--   This identity turns the linearized assortment objective $h_z$ into a directed cut function, so that max-dicut algorithms apply to assortment optimization.
--
--   Differences from the source:
--   - reading: v₀ is the no-purchase weight, with no sign stated (p.789) → v₀ > 0 (field of PCLInstance); reason: the paper divides by v₀ (fixed point of g(·)/v₀, p.792); with v₀ = 0 the framework degenerates
--   - encoding: γ_ij ∈ [0, 1] (p.789) → γ_ij ∈ (0, 1] for i ≠ j; reason: v_i^{1/γ_ij} is undefined at γ_ij = 0; this excludes only the undefined case
--   - encoding: R_ij(x) = 0/0 for an empty nest → Lean's 0/0 = 0; reason: the nest then has weight V_ij(x)^{γ_ij} = 0 (γ_ij > 0), so it contributes nothing either way
--   - encoding: vertices [n+1] with dummy n+1, products [n] → Option (Fin n) with none the dummy, Fin n; reason: relabelling; same graph
--   - reading: edge weights (4)–(6), whose ξ⁻/ψ⁻ subscripts disagree with the prose on pp.790–791 → closed forms: the pair (i,j) puts r̄_i a/D on (i,n+1), r̄_j b/D on (j,n+1), v_i r̄_i − r̄_i a/D on (i,j), v_j r̄_j − r̄_j b/D on (j,i); reason: the closed forms are unambiguous and make Lemma 1 hold; the subscripts are a typesetting inconsistency
-- source:
--   Ghuge, Kwon, Nagarajan, Sharma, Constrained Assortment Optimization Under the Paired Combinatorial Logit Model, Oper. Res. 70(2) (2022), Lemma 1, p.791 (PDF p.7)

import Mathlib
import Definitions.Def_PCLAssort_PCLInstance
import Definitions.Def_PCLAssort_hz
import Definitions.Def_PCLAssort_cutValue
import Definitions.Def_PCLAssort_pclEdges
import Definitions.Def_PCLAssort_pclWeight

namespace PCLAssort

/-- Lemma 1 (Ghuge, Kwon, Nagarajan, Sharma, Oper. Res. 70(2), 2022, p.791): for any subset `S ⊆ [n]`, `h_z(1_S) = ∑_{(i,j)∈E: i∈S, j∉S} w_ij(z)`,
where `1_S ∈ {0,1}^n` is the indicator vector of `S`.

**Formalization Note.** The cut is taken in `G_z` (vertices `Option (Fin n)`, dummy `none`), of the
vertex set `S.image some`, which never contains the dummy. Weights are the closed forms of
`pclWeight` (the ξ⁻/ψ⁻ subscript repair of (4)–(5)). -/
theorem lemma_1_hz_eq_cut {n : ℕ} (I : PCLInstance n) (z : ℝ) (S : Finset (Fin n)) :
    hz I z S = cutValue (pclEdges n) (pclWeight I z) (S.image some) := by sorry

end PCLAssort
