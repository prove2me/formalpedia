-- Prove2me | Theorems.Thm_PunctSketch_lemma_4_2
-- name    : PunctSketch.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:44:55.214942+00:00
-- url     : https://prove2.me/theorems/adcab55f-0879-447f-a3a8-2a067fb16937
-- title:
--   Lemma 4.2, p.12 — aggregation over a set $C$ (corrected: $\mathrm{sgn}(u-v)$)
-- statement:
--   For any set of vertices $C\subseteq V\setminus F$, with $|F|<k$, and each coordinate $t\in\{0,\dots,2d+k-1-|F|\}$,
--   $$\sum_{v\in C}\tilde{\boldsymbol s}_F(v)_t=\sum_{\substack{\{v,u\}\in E:\\ v\in C,\ u\notin C\cup F}}\mathrm{sgn}(u-v)\,(\alpha_v\alpha_u)^t\,P_F(\alpha_v)\,P_F(\alpha_u).$$
--   Edges inside $C$ cancel, so the sum is a sketch of a vector supported exactly on the punctured boundary $\partial_{-F}C$.
--
--   **Formalization Note** The right side is a double sum over $v\in C$ and $u\notin C\cup F$, so each edge is counted once, from its endpoint in $C$.
--
--   Differences from the source:
--   - correction: sgn(v − u) on the right side → sgn(u − v); reason: follows from the correction of Lemma 4.1; the same counterexample: n = 2, E = {{1,2}}, d = 0, k = 1, F = ∅, v = 1, t = 0, where the left side is 1 and the printed right side is −1, with C = {1}
--   - generalization: α_1, …, α_n the images of the first n primes → any points α : Fin n → ZMod Q; reason: the identity uses nothing about the points; the primes are one instance
--   - encoding: vertices [n] = {1, …, n} → Fin n, zero-indexed; reason: Lean convention; same instances
-- source:
--   Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity, STOC 2027 submission (manuscript sha256 a630f88815653b5f1b35579cbfa2100b617a4d540f009489027b8c55f65e1a2c), Lemma 4.2, p.12 (PDF p.13)

import Mathlib
import Definitions.Def_PunctSketch_sketch
import Definitions.Def_PunctSketch_puncture

namespace PunctSketch

open Classical in
/-- **Lemma 4.2 (corrected: sgn(u − v)).** Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, *Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission (manuscript sha256 a630f888…), Lemma 4.2, p.12. For any set of vertices
`C ⊆ V ∖ F` and each coordinate `t ∈ {0, …, 2d + k − 1 − |F|}`,
`Σ_{v∈C} 𝒔̃_F(v)_t = Σ_{{v,u}∈E: v∈C, u∉C∪F} sgn(u − v) (α_v α_u)^t P_F(α_v) P_F(α_u)`.

**Formalization Note.** The right side is written as a double sum over `v ∈ C` and `u ∉ C ∪ F`, so
each edge is counted once, from its endpoint in `C`, which fixes the orientation of the sign. The sign
is corrected as in Lemma 4.1. -/
theorem lemma_4_2 {n Q : ℕ} [Fact Q.Prime] (α : Fin n → ZMod Q) (G : SimpleGraph (Fin n))
    (F C : Finset (Fin n)) (d k : ℕ) (hF : F.card < k) (hC : Disjoint C F) (t : ℕ)
    (ht : t + F.card < 2 * d + k) :
    ∑ v ∈ C, puncture α F (sketch G α v) v t =
      ∑ v ∈ C, ∑ u ∈ Finset.univ.filter (fun u => G.Adj v u ∧ u ∉ C ∧ u ∉ F),
        ((sgn u v : ℤ) : ZMod Q) * (α v * α u) ^ t * (puncturePoly α F).eval (α v) *
          (puncturePoly α F).eval (α u) := by sorry

end PunctSketch
