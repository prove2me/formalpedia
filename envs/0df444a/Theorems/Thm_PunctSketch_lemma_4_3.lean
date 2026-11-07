-- Prove2me | Theorems.Thm_PunctSketch_lemma_4_3
-- name    : PunctSketch.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:44:30.815693+00:00
-- url     : https://prove2.me/theorems/acd64f67-43a4-4fb1-9c91-a5cbe590384c
-- title:
--   Lemma 4.3, p.13 — the artificial fingerprint of a vertex
-- statement:
--   For any node $v\notin F$, with $|F|<k$, and each coordinate $t\in\{0,\dots,c+k-1-|F|\}$,
--   $$\tilde{\boldsymbol f}_F(v)_t=\sum_{u\in N(v)\setminus F}\mathrm{sgn}(v-u)\,\boldsymbol r_{\{v,u\}}\,(\alpha_v\alpha_u)^t\,P_F(\alpha_v)\,P_F(\alpha_u).$$
--   Summed over a set $C$, the edges inside $C$ cancel, since $u$ and $v$ read the same $\boldsymbol r_{\{v,u\}}$.
--
--   Differences from the source:
--   - reading: the left side is printed as 𝒇̃_F(v), without t → 𝒇̃_F(v)_t; reason: the rest of the sentence quantifies over t, and the right side depends on t
--   - generalization: α the images of the first n primes, 𝒓 with nonzero entries → any points α and any 𝒓 : Sym2 (Fin n) → ZMod Q; reason: the identity uses nothing about them; the source’s values are one instance
--   - encoding: vertices [n] = {1, …, n} → Fin n, zero-indexed; reason: Lean convention; same instances
-- source:
--   Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity, STOC 2027 submission (manuscript sha256 a630f88815653b5f1b35579cbfa2100b617a4d540f009489027b8c55f65e1a2c), Lemma 4.3, p.13 (PDF p.14)

import Mathlib
import Definitions.Def_PunctSketch_fingerprint
import Definitions.Def_PunctSketch_puncture

namespace PunctSketch

open Classical in
/-- **Lemma 4.3.** Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, *Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission (manuscript sha256 a630f888…), Lemma 4.3, p.13. For any node `v ∉ F` and each coordinate
`t ∈ {0, …, c + k − 1 − |F|}`,
`𝒇̃_F(v)_t = Σ_{u∈N(v)∖F} sgn(v − u) 𝒓_{v,u} (α_v α_u)^t P_F(α_v) P_F(α_u)`.

**Formalization Note.** The page prints `𝒇̃_F(v)` without the coordinate `t`; the rest of the sentence
fixes it. The statement holds for any points `α` and any `𝒓`. -/
theorem lemma_4_3 {n Q : ℕ} [Fact Q.Prime] (α : Fin n → ZMod Q) (r : Sym2 (Fin n) → ZMod Q)
    (G : SimpleGraph (Fin n)) (F : Finset (Fin n)) (c k : ℕ) (hF : F.card < k) (v : Fin n)
    (hv : v ∉ F) (t : ℕ) (ht : t + F.card < c + k) :
    puncture α F (fingerprint G α r v) v t =
      ∑ u ∈ Finset.univ.filter (fun u => G.Adj v u ∧ u ∉ F),
        ((sgn v u : ℤ) : ZMod Q) * r s(v, u) * (α v * α u) ^ t * (puncturePoly α F).eval (α v) *
          (puncturePoly α F).eval (α u) := by sorry

end PunctSketch
