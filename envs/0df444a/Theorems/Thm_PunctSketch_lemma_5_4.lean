-- Prove2me | Theorems.Thm_PunctSketch_lemma_5_4
-- name    : PunctSketch.lemma_5_4
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T10:44:24.187752+00:00
-- url     : https://prove2.me/theorems/47a5e7b3-e296-4e2c-b9af-e9f17e9c5b98
-- title:
--   Lemma 5.4, p.19 — the alternate artificial fingerprint
-- statement:
--   Let $\Phi$ be a matrix over $\mathbb F_Q$ and let $\boldsymbol p$ satisfy $\boldsymbol p^{\mathsf T}\Phi_z=0$ for all $z\in F$; write $z(v)=\boldsymbol p^{\mathsf T}\Phi_v$. For any node $v\notin F$,
--   $$z(v)\,\boldsymbol p^{\mathsf T}f(v)=\sum_{u\in N(v)\setminus F}\mathrm{sgn}(v-u)\,z(v)\,z(u).$$
--   With $\boldsymbol p=\boldsymbol p_t$ this is the lemma's identity in the coordinate $t\in\{0,\dots,c\}$.
--
--   Differences from the source:
--   - generalization: p_0, …, p_c linearly independent in the left kernel of Φ_F, Φ with c + k rows → one vector p in the left kernel of Φ_F, Φ with any number of rows; reason: applied to each p_t this gives every coordinate; the independence is not used
--   - reading: eq. (8) prints z_j(v) → z_t(v); reason: a misprint: the proof of the lemma expands z_t(v)
--   - encoding: vertices [n] = {1, …, n} → Fin n, zero-indexed; reason: Lean convention; same instances
-- source:
--   Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity, STOC 2027 submission (manuscript sha256 a630f88815653b5f1b35579cbfa2100b617a4d540f009489027b8c55f65e1a2c), Lemma 5.4, p.19 (PDF p.20)

import Mathlib
import Definitions.Def_PunctSketch_altFingerprint

namespace PunctSketch

open Classical in
/-- **Lemma 5.4.** Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, *Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission (manuscript sha256 a630f888…), Lemma 5.4, p.19. For any node `v ∉ F` and each coordinate `t ∈ {0, …, c}`,
`f̃_F(v)_t = Σ_{u∈N(v)∖F} sgn(v − u) z_t(v) z_t(u)`.

**Formalization Note.** Stated for one kernel vector `p = 𝒑_t` with `𝒑ᵀΦ_F = 𝟎`, which is all the identity
uses, so it covers every coordinate `t`; the page's linear independence of the `𝒑_t` is not needed. The
number of rows of `Φ` is `D`, which is `c + k` on the page. -/
theorem lemma_5_4 {n D Q : ℕ} [Fact Q.Prime] (G : SimpleGraph (Fin n)) (Φ : Fin D → Fin n → ZMod Q)
    (F : Finset (Fin n)) (p : Fin D → ZMod Q) (hp : ∀ z ∈ F, altZ Φ p z = 0) (v : Fin n)
    (hv : v ∉ F) :
    altPunctured G Φ p v =
      ∑ u ∈ Finset.univ.filter (fun u => G.Adj v u ∧ u ∉ F),
        ((sgn v u : ℤ) : ZMod Q) * altZ Φ p v * altZ Φ p u := by sorry

end PunctSketch
