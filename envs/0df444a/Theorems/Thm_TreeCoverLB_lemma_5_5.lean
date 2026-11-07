-- Prove2me | Theorems.Thm_TreeCoverLB_lemma_5_5
-- name    : TreeCoverLB.lemma_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:24:53.649841+00:00
-- url     : https://prove2.me/theorems/fe61dbe0-e360-4bd9-89b1-5e9026536e0f
-- title:
--   Lemma 5.5: a free complex of dimension $\le d$ maps equivariantly to $|E_dH|$
-- statement:
--   Let $H$ be a nontrivial finite group, and let $K$ be a nonempty finite abstract simplicial complex with a simplicial $H$-action that is free on $|K|$. If $\dim K\le d$, then there is a continuous $H$-equivariant map
--   $$
--   |K|\longrightarrow|E_dH| .
--   $$
--
--   Differences from the source:
--   - reading: K nonempty → K has a nonempty face; reason: every complex contains ∅, so 'nonempty' must mean |K| ≠ ∅
--   - encoding: a simplicial H-action on K, free on |K|; dim K ≤ d → an action of H on the vertex type (additive notation) mapping faces to faces, h · µ = µ only for h = 0 on |K|; every face has at most d + 1 vertices; reason: definitions 3.2 and 3.8 and §3.4 written out
-- source:
--   Chen, Huang, Tan, Xu, Improved Lower Bounds on Tree Covers, arXiv:2607.27264 (version of October 31, 2026), Lemma 5.5, p.19 (PDF p.21); cited from [Mat03, Proposition 6.2.4(v)]

import Mathlib
import Definitions.Def_TreeCoverLB_realization
import Definitions.Def_TreeCoverLB_EJoin

open Classical

namespace TreeCoverLB

/-- **Lemma 5.5** (Chen, Huang, Tan, Xu, *Improved Lower Bounds on Tree Covers*, arXiv:2607.27264 (version of October 31, 2026), Lemma 5.5, p.19 (PDF p.21); cited from [Mat03, Proposition 6.2.4(v)]): let
`H` be a nontrivial finite group, and let `K` be a nonempty finite abstract simplicial complex with a
simplicial `H`-action that is free on `|K|`. If `dim K ≤ d`, then there is a continuous
`H`-equivariant map `|K| → |E_dH|`.

**Formalization Note** `H` is written additively (not necessarily commutative) and acts on the finite
vertex type `V`; the action is simplicial (`h · σ ∈ K` for `σ ∈ K`) and extended to `|K|` by
`ptAct`. "Nonempty" means `K` has a nonempty face; "free on `|K|`" is about points of `|K|`;
`dim K ≤ d` means every face has at most `d + 1` vertices. `H` acts on `E_dH` layerwise. -/
theorem lemma_5_5 {H V : Type*} [AddGroup H] [Fintype H] [Nontrivial H] [Fintype V]
    [AddAction H V] (K : Set (Finset V)) (hK : IsASC K) (hne : ∃ σ ∈ K, σ.Nonempty)
    (hsimp : ∀ h : H, ∀ σ ∈ K, σ.image (fun v => h +ᵥ v) ∈ K)
    (hfree : ∀ h : H, ∀ μ ∈ realization K, ptAct h μ = μ → h = 0)
    (d : ℕ) (hdim : ∀ σ ∈ K, σ.card ≤ d + 1) :
    ∃ F : (V → ℝ) → (Fin (d + 1) × H → ℝ),
      ContinuousOn F (realization K) ∧
      Set.MapsTo F (realization K) (realization (EJoin d H)) ∧
      ∀ h : H, ∀ μ ∈ realization K, F (ptAct h μ) = ejoinAct h (F μ) := by sorry

end TreeCoverLB
