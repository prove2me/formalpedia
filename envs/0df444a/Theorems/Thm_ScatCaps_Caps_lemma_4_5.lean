-- Prove2me | Theorems.Thm_ScatCaps_Caps_lemma_4_5
-- name    : ScatCaps.Caps.lemma_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:06:01.194915+00:00
-- url     : https://prove2.me/theorems/413ae121-a180-4dbd-94d8-31c322058d42
-- title:
--   Lemma 4.5, p. 20 — the product of maximal translation caps in AG(r, 2^t) and AG(r̄, 2^t) is a maximal translation cap in AG(r + r̄, 2^t)
-- statement:
--   Let $q = 2^t$, $t > 1$. If $\mathcal K_G$ is a maximal translation cap in $AG(r, 2^t)$ and $\mathcal K_H$ is a maximal translation cap in $AG(\bar r, 2^t)$, then
--
--   $$\mathcal K_G \times \mathcal K_H \text{ is a maximal translation cap in } AG(r + \bar r, 2^t),$$
--
--   where $\mathcal K_G \times \mathcal K_H$ is the set of concatenated vectors $(a_1, \dots, a_r, b_1, \dots, b_{\bar r})$ with $(a_i) \in G$, $(b_j) \in H$.
--
--   Iterating this lemma with the parabola extends a maximal translation cap in $AG(3, q)$ to one in $AG(n-1, q)$.
--
--   **Formalization Note** The hypothesis $t > 1$ is carried because the paper defines maximal translation caps only for $t > 1$ (p. 20).
-- source:
--   Bartoli, Giulietti, Marino & Polverino, Maximum scattered linear sets and complete caps in Galois spaces, arXiv:1512.07467v1, p. 20, Lemma 4.5 (citing [6, Proposition 2.8])

import Mathlib
import Definitions.Def_ScatCaps_Caps_Model

namespace ScatCaps.Caps

theorem lemma_4_5 (K : Type*) [Field K] [Fintype K] (t : ℕ)
    (hK : Fintype.card K = 2 ^ t) (ht : 1 < t) {r r' : ℕ}
    (G : AddSubgroup (Fin r → K)) (H : AddSubgroup (Fin r' → K))
    (hG : IsMaximalTranslationCap (KG G)) (hH : IsMaximalTranslationCap (KG H)) :
    IsMaximalTranslationCap (capProd (KG G) (KG H)) := by sorry

end ScatCaps.Caps
