-- Prove2me | Theorems.Thm_PunctSketch_lemma_4_1
-- name    : PunctSketch.lemma_4_1
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T10:44:43.754203+00:00
-- url     : https://prove2.me/theorems/d6291756-92ec-4292-a07c-9944fc78b85d
-- title:
--   Lemma 4.1, p.11 — the artificial sketch of a vertex (corrected: $\mathrm{sgn}(u-v)$)
-- statement:
--   For any vertex $v\notin F$, with $|F|<k$, and each coordinate $t\in\{0,\dots,2d+k-1-|F|\}$,
--   $$\tilde{\boldsymbol s}_F(v)_t=\sum_{u\in N(v)\setminus F}\mathrm{sgn}(u-v)\,(\alpha_v\alpha_u)^t\,P_F(\alpha_v)\,P_F(\alpha_u).$$
--   The right side no longer involves neighbours in $F$, and its coefficient is symmetric in $u$ and $v$ apart from the sign. So the artificial sketch is a sketch of a scaled signed incidence vector of $G\setminus F$.
--
--   Differences from the source:
--   - correction: sgn(v − u) on the right side → sgn(u − v); reason: the sketch is defined with sgn(u − v), and the page's proof switches sign in its first line; counterexample: n = 2, E = {{1,2}}, d = 0, k = 1, F = ∅, v = 1, t = 0, where the left side is 1 and the printed right side is −1
--   - generalization: α_1, …, α_n the images of the first n primes → any points α : Fin n → ZMod Q; reason: the identity uses nothing about the points; the primes are one instance
--   - encoding: vertices [n] = {1, …, n} → Fin n, zero-indexed; reason: Lean convention; same instances
-- source:
--   Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity, STOC 2027 submission (manuscript sha256 a630f88815653b5f1b35579cbfa2100b617a4d540f009489027b8c55f65e1a2c), Lemma 4.1, p.11 (PDF p.12)

import Mathlib
import Definitions.Def_PunctSketch_sketch
import Definitions.Def_PunctSketch_puncture

namespace PunctSketch

open Classical in
/-- **Lemma 4.1 (corrected: sgn(u − v)).** Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, *Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission (manuscript sha256 a630f888…), Lemma 4.1, p.11. For any vertex `v ∉ F` and each
coordinate `t ∈ {0, …, 2d + k − 1 − |F|}`,
`𝒔̃_F(v)_t = Σ_{u∈N(v)∖F} sgn(u − v) (α_v α_u)^t P_F(α_v) P_F(α_u)`.

**Formalization Note.** The page prints `sgn(v − u)`, which contradicts the definition of `𝒔` on the
same page: for `n = 2`, `E = {{1,2}}`, `F = ∅`, `v = 1`, `t = 0`, the left side is `1` and the printed
right side is `−1`. The statement holds for any points `α`. -/
theorem lemma_4_1 {n Q : ℕ} [Fact Q.Prime] (α : Fin n → ZMod Q) (G : SimpleGraph (Fin n))
    (F : Finset (Fin n)) (d k : ℕ) (hF : F.card < k) (v : Fin n) (hv : v ∉ F) (t : ℕ)
    (ht : t + F.card < 2 * d + k) :
    puncture α F (sketch G α v) v t =
      ∑ u ∈ Finset.univ.filter (fun u => G.Adj v u ∧ u ∉ F),
        ((sgn u v : ℤ) : ZMod Q) * (α v * α u) ^ t * (puncturePoly α F).eval (α v) *
          (puncturePoly α F).eval (α u) := by sorry

end PunctSketch
