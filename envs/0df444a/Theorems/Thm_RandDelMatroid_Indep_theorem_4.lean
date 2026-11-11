-- Prove2me | Theorems.Thm_RandDelMatroid_Indep_theorem_4
-- name    : RandDelMatroid.Indep.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T18:29:10.768811+00:00
-- url     : https://prove2.me/theorems/1b6dd266-710b-4da9-982b-dee101661a0e
-- title:
--   Theorem 4 (Karger) — at most $n^{2\alpha}$ cuts of weight at most $\alpha\lambda$
-- statement:
--   Let $G=(V,E)$ be a connected undirected (multi)graph with $n=|V|\ge2$ vertices and nonnegative edge weights $w:E\to\mathbb R_{\ge0}$, whose minimum cut weight
--
--   $$\lambda=\min\{w(\delta_G(S)) : \emptyset\subsetneq S\subsetneq V\}$$
--
--   is positive. Then for every $\alpha\ge1$, the number of cuts $\delta_G(S)$ with $w(\delta_G(S))\le\alpha\lambda$ is at most $n^{2\alpha}$.
--
--   The paper cites this bound of Karger [Kar93, Kar95]; it counts the light circuits at a cographic node (Lemma 18), where the circuits are bonds of a graph.
--
--   **Formalization Note** The graph is an endpoint map on finite types `V` and `β` (all of `β` are edges; parallel edges and loops allowed, loops never lie in a cut). $\alpha$ is real and $n^{2\alpha}$ is a real power.
--
--   Differences from the source:
--   - reading: the number of cuts δ_G(S) with w(δ_G(S)) ≤ αλ → the number of distinct edge sets δ_G(S), ∅ ⊊ S ⊊ V, with weight ≤ αλ; reason: cuts are counted as edge sets, over the same vertex sets S as in the definition of λ
--   - encoding: undirected graph G = (V, E) → finite multigraph given by ends : β → Sym2 V, connected via its spanning simple graph; reason: Lemma 18 applies the theorem to graphs with parallel edges (p. 27, p. 30); simple graphs are a special case
-- source:
--   Karthekeyan Chandrasekaran, Chandra Chekuri, Weihao Zhu, STOC 2027 submission #536 (October 2026), p. 9, Theorem 4 ([Kar93, Kar95])

import Mathlib
import Definitions.Def_RandDelMatroid_Indep_Graphic

set_option autoImplicit false

open scoped NNReal

namespace RandDelMatroid.Indep

/-- Theorem 4 (Karger [Kar93, Kar95], p. 9). Let `G = (V, E)` be a connected finite multigraph
with `n = |V| ≥ 2` vertices and nonnegative edge weights `w`, whose minimum cut weight
`λ = min {w(δ(S)) : ∅ ⊊ S ⊊ V}` is positive. Then for every real `α ≥ 1`, the number of (distinct)
cuts `δ(S)`, `∅ ⊊ S ⊊ V`, with `w(δ(S)) ≤ αλ` is at most `n^{2α}`. -/
theorem theorem_4 {V β : Type} [Fintype V] [Fintype β] (ends : β → Sym2 V) (w : β → ℝ≥0)
    (hconn : (spanningGraph ends Set.univ).Connected) (hn : 2 ≤ Fintype.card V) (lam : ℝ)
    (hlam : IsLeast {c : ℝ | ∃ S : Set V, S.Nonempty ∧ S ≠ Set.univ ∧
      c = setWeight w (cut ends Set.univ S)} lam)
    (hpos : 0 < lam) (α : ℝ) (hα : 1 ≤ α) :
    (({C : Set β | ∃ S : Set V, S.Nonempty ∧ S ≠ Set.univ ∧ C = cut ends Set.univ S ∧
      setWeight w C ≤ α * lam}).ncard : ℝ) ≤ (Fintype.card V : ℝ) ^ (2 * α) := by sorry

end RandDelMatroid.Indep
