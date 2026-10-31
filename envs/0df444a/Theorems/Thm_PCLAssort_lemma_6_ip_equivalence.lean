-- Prove2me | Theorems.Thm_PCLAssort_lemma_6_ip_equivalence
-- name    : PCLAssort.lemma_6_ip_equivalence
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:22:01.649272+00:00
-- url     : https://prove2.me/theorems/b98fcea3-6c41-4e47-bb55-fe4d25d8ed74
-- title:
--   Lemma 6 — IP$_1(z)$ and IP$_2(z)$ are equivalent, and IP$_2(z)$ is max-dicut on $\tilde G_z$
-- statement:
--   Let $\mathcal F$ be a downward-closed family of assortments containing $\emptyset$. For all $z\in\mathbb R$:
--
--   1. the optimal value of IP$_1(z)$ equals the optimal value of IP$_2(z)$;
--   2. the optimal value of IP$_2(z)$ equals the optimal max-dicut value on $\tilde G_z$ (the nonnegative-weight edges of $G_z$) subject to the constraints that the dummy vertex is not selected and that the set of chosen vertices lies in $\mathcal F$.
--
--   Together with Lemma 5, $f(z)$ is a constrained max-dicut value on a graph with nonnegative weights.
--
--   Differences from the source:
--   - reading: 𝓕 downward closed (p.790) → 𝓕 downward closed and ∅ ∈ 𝓕; reason: every constraint family of the paper contains ∅; with 𝓕 = ∅ the optimal values are undefined
--   - reading: v₀ is the no-purchase weight, with no sign stated (p.789) → v₀ > 0 (field of PCLInstance); reason: the paper divides by v₀ (fixed point of g(·)/v₀, p.792); with v₀ = 0 the framework degenerates
--   - encoding: γ_ij ∈ [0, 1] (p.789) → γ_ij ∈ (0, 1] for i ≠ j; reason: v_i^{1/γ_ij} is undefined at γ_ij = 0; this excludes only the undefined case
--   - encoding: R_ij(x) = 0/0 for an empty nest → Lean's 0/0 = 0; reason: the nest then has weight V_ij(x)^{γ_ij} = 0 (γ_ij > 0), so it contributes nothing either way
--   - encoding: vertices [n+1] with dummy n+1, products [n] → Option (Fin n) with none the dummy, Fin n; reason: relabelling; same graph
--   - reading: edge weights (4)–(6), whose ξ⁻/ψ⁻ subscripts disagree with the prose on pp.790–791 → closed forms: the pair (i,j) puts r̄_i a/D on (i,n+1), r̄_j b/D on (j,n+1), v_i r̄_i − r̄_i a/D on (i,j), v_j r̄_j − r̄_j b/D on (j,i); reason: the closed forms are unambiguous and make Lemma 1 hold; the subscripts are a typesetting inconsistency
-- source:
--   Ghuge, Kwon, Nagarajan, Sharma, Constrained Assortment Optimization Under the Paired Combinatorial Logit Model, Oper. Res. 70(2) (2022), Lemma 6, p.792 (PDF p.8)

import Mathlib
import Definitions.Def_PCLAssort_PCLInstance
import Definitions.Def_PCLAssort_DownwardClosed
import Definitions.Def_PCLAssort_ip1Value
import Definitions.Def_PCLAssort_ip2Value
import Definitions.Def_PCLAssort_constrDicutValue
import Definitions.Def_PCLAssort_pclWeight
import Definitions.Def_PCLAssort_tildeEdges

namespace PCLAssort

/-- Lemma 6 (Ghuge, Kwon, Nagarajan, Sharma, Oper. Res. 70(2), 2022, p.792): the formulations IP₁(z) and IP₂(z) are equivalent, that is, for all
`z ∈ ℝ`, the optimal value of IP₁(z) is the same as the optimal value of IP₂(z). Moreover, for each
`z ∈ ℝ`, the optimal value of IP₂(z) equals the optimal max-dicut value on `G̃_z` subject to the
constraints that the dummy vertex is not selected and that the set of chosen vertices lies in `𝓕`.

**Formalization Note.** `G̃_z` keeps the edges of `G_z` with nonnegative weight (`tildeEdges`). `𝓕`
is any downward-closed family containing `∅` (p.790). -/
theorem lemma_6_ip_equivalence {n : ℕ} (I : PCLInstance n) (F : Set (Finset (Fin n)))
    (hF : DownwardClosed F) :
    ∀ z : ℝ, ip1Value I F z = ip2Value I F z ∧
      ip2Value I F z = constrDicutValue (tildeEdges I z) (pclWeight I z) F := by sorry

end PCLAssort
