-- Prove2me | Theorems.Thm_SunGroupIso_Class2_lemma_3_1
-- name    : SunGroupIso.Class2.lemma_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:06:02.687076+00:00
-- url     : https://prove2.me/theorems/6160be91-1afc-4a83-99eb-36b9eefc573a
-- title:
--   Lemma 3.1 — commutator-and-power criterion for isomorphism of class-2 p-groups
-- statement:
--   Let $G,H$ be finite $p$-groups of class 2 whose centres both have rank $k$ and whose central quotients both have rank $k'$; $\ell=k+k'$. Then $G\cong H$ if and only if there are $g_1,\dots,g_\ell\in G$, $h_1,\dots,h_\ell\in H$ with: (1) $Z(G)=\bigoplus_{i\le k}\langle g_i\rangle$, $Z(H)=\bigoplus_{i\le k}\langle h_i\rangle$, $\mathrm{ord}(g_i)=\mathrm{ord}(h_i)$; (2) $G/Z(G)=\bigoplus_{i>k}\langle\tilde g_i\rangle$, $H/Z(H)=\bigoplus_{i>k}\langle\tilde h_i\rangle$, $\mathrm{ord}(\tilde g_i)=\mathrm{ord}(\tilde h_i)$; (3) with $t_i=\mathrm{ord}(g_i)$ ($i\le k$), $t_i=\mathrm{ord}(\tilde g_i)$ ($i>k$) and $f(g_1^{m_1}\cdots g_\ell^{m_\ell})=h_1^{m_1}\cdots h_\ell^{m_\ell}$ ($0\le m_i<t_i$): (a) $f(g_i^{t_i})=f(g_i)^{t_i}$ for $i>k$, (b) $f([g_i,g_j])=[f(g_i),f(g_j)]$ for all $i,j$. Furthermore, whenever these three conditions hold, $f$ is an isomorphism (some $\varphi:G\cong H$ agrees with $f$ everywhere).
--
--   Differences from the source:
--   - encoding: one-based indices → zero-based Fin indices (or the one-based helper at1); reason: a bijective reindexing
--   - encoding: 'f is an isomorphism' → ∃ φ : G ≃* H, ∀ x, φ x = f x; reason: the same statement about the map f
-- source:
--   Sun 2026, arXiv:2611.05920 (held version, sha256 22193308…), Lemma 3.1, p. 11 (PDF p. 13)

import Mathlib
import Definitions.Def_SunGroupIso_Class2_Basic

set_option autoImplicit false

open scoped Classical commutatorElement

namespace SunGroupIso.Class2

open ExponomialAssortment.FPTAS (encodeNat)
open GroupIsoPoly (encPair cayley)

/-- **Lemma 3.1** (Sun 2026, arXiv:2611.05920 (held version, sha256 22193308…), Lemma 3.1, p. 11, PDF p. 13). Let `G, H` be finite `p`-groups of class 2
whose centres have rank `k` and whose central quotients have rank `k'`, `ℓ = k + k'`. Then `G ≅ H` if and
only if there are `g_1, …, g_ℓ ∈ G`, `h_1, …, h_ℓ ∈ H` satisfying the three conditions `CPConds`
(matched decompositions of the centres and central quotients; the normal-form map `f` preserves the
central powers `g_i^{t_i}`, `i > k`, and all commutators `[g_i, g_j]`). Furthermore, whenever the three
conditions hold, `f` is an isomorphism. -/
theorem lemma_3_1 {p : ℕ} (hp : p.Prime) {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (hG : IsPGroupClass2 p G) (hH : IsPGroupClass2 p H) (k k' : ℕ)
    (hZG : abRank (Subgroup.center G) = k) (hZH : abRank (Subgroup.center H) = k)
    (hQG : abRank (⊤ : Subgroup (Qt G)) = k') (hQH : abRank (⊤ : Subgroup (Qt H)) = k') :
    (Nonempty (G ≃* H) ↔
      ∃ (g : Fin (k + k') → G) (h : Fin (k + k') → H), CPConds k k' g h) ∧
    ∀ (g : Fin (k + k') → G) (h : Fin (k + k') → H), CPConds k k' g h →
      ∃ φ : G ≃* H, ∀ x : G,
        φ x = nfMap g h (fun i => if i.val < k then orderOf (g i) else orderOf (tl (g i))) x := by sorry

end SunGroupIso.Class2
