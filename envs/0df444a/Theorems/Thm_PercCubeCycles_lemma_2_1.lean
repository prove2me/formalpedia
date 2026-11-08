-- Prove2me | Theorems.Thm_PercCubeCycles_lemma_2_1
-- name    : PercCubeCycles.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:33:19.417578+00:00
-- url     : https://prove2.me/theorems/1156e156-9140-4c7b-93b2-33d079bde04b
-- title:
--   Lemma 2.1 — $t(v,k)\le k^{k-2}\Delta^{k-1}/(k-1)!\le(e\Delta)^{k-1}$ rooted trees
-- statement:
--   Let $G$ be a graph of maximum degree $\Delta$, let $v\in V(G)$ and let $k\ge1$. Let $t(v,k)$ be the number of trees in $G$ with $k$ vertices containing $v$. Then
--   $$t(v,k)\le\frac{k^{k-2}\Delta^{k-1}}{(k-1)!}\le(e\Delta)^{k-1}.$$
--   This count enters every union bound over connected sets in the paper.
--
--   Differences from the source:
--   - generalization: $G$ has maximum degree $\Delta$ → every degree of $G$ is at most $\Delta$; reason: a graph of maximum degree exactly $\Delta$ satisfies the hypothesis
--   - encoding: a graph → a graph on a finite type; reason: the paper considers finite graphs
--   - encoding: $k^{k-2}$ at $k=1$ → natural-number exponent, so the value is $1$; reason: equal to $1^{-1}$
-- source:
--   Anastos, Linear-length cycles in the supercritical percolated hypercube, STOC 2027 submission (sha256 14e6f0eeea86205c661b9ec5b7259d5e903f4bcfacef3946a425ea6e60e837ae), Lemma 2.1 (citing [7], Lemma 2), p.6

import Mathlib
import Definitions.Def_PercCubeCycles_GraphNotation

set_option autoImplicit false

namespace PercCubeCycles

/-- Lemma 2.1, p.6 ([7], Lemma 2), Anastos, *Linear-length cycles in the supercritical percolated hypercube*, STOC 2027 submission (sha256 14e6f0ee…). For a finite graph `G` of maximum degree `Δ`, a vertex `v`
and `k ≥ 1`, the number `t(v, k)` of trees in `G` with `k` vertices that contain `v` satisfies
`t(v, k) ≤ k^{k−2} Δ^{k−1} / (k − 1)! ≤ (eΔ)^{k−1}`.

**Formalization Note.** A tree in `G` is a `G.Subgraph` whose coercion is a tree. `k^{k−2}` at `k = 1` is
`1`, the value of `1^{−1}`. The hypothesis is `deg ≤ Δ`, which covers maximum degree exactly `Δ`. -/
theorem lemma_2_1 {V : Type*} [Fintype V] (G : SimpleGraph V) (Δ : ℕ) (hΔ : ∀ u, deg G u ≤ Δ)
    (v : V) (k : ℕ) (hk : 1 ≤ k) :
    ({T : G.Subgraph | T.coe.IsTree ∧ v ∈ T.verts ∧ T.verts.ncard = k}.ncard : ℝ)
        ≤ (k : ℝ) ^ (k - 2) * (Δ : ℝ) ^ (k - 1) / ((k - 1).factorial : ℝ) ∧
      (k : ℝ) ^ (k - 2) * (Δ : ℝ) ^ (k - 1) / ((k - 1).factorial : ℝ)
        ≤ (Real.exp 1 * Δ) ^ (k - 1) := by sorry

end PercCubeCycles
