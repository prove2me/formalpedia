-- Prove2me | Theorems.Thm_ScatCaps_Caps_lemma_4_6
-- name    : ScatCaps.Caps.lemma_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:05:47.848859+00:00
-- url     : https://prove2.me/theorems/eb447171-f248-4844-9181-9cabfebe990f
-- title:
--   Lemma 4.6, p. 20 — doubling: if 𝒦_G is a maximal translation cap in AG(r, 2^t) then 𝒦_{G×{0,1}} is a complete cap in AG(r + 1, 2^t)
-- statement:
--   Let $q = 2^t$, $t > 1$, and let $G$ be an additive subgroup of $\mathbb F_{2^t}^r$. If $\mathcal K_G$ is a maximal translation cap in $AG(r, 2^t)$, then
--
--   $$\mathcal K_{G \times \{0,1\}} = \{(a_1, \dots, a_r, c) : (a_1, \dots, a_r) \in G,\ c \in \{0, 1\}\}$$
--
--   is a complete cap in $AG(r + 1, 2^t)$.
--
--   This doubling construction produces the complete cap of Theorem 1.3 from a maximal translation cap in $AG(n-1, q)$; its size is twice that of $\mathcal K_G$.
--
--   **Formalization Note** The hypothesis $t > 1$ is carried: for $t = 1$ every subset of $AG(r+1, 2)$ is a cap and the statement fails.
-- source:
--   Bartoli, Giulietti, Marino & Polverino, Maximum scattered linear sets and complete caps in Galois spaces, arXiv:1512.07467v1, p. 20, Lemma 4.6 (citing [6, Corollary 2.12])

import Mathlib
import Definitions.Def_ScatCaps_Caps_Model

namespace ScatCaps.Caps

theorem lemma_4_6 (K : Type*) [Field K] [Fintype K] (t : ℕ)
    (hK : Fintype.card K = 2 ^ t) (ht : 1 < t) {r : ℕ}
    (G : AddSubgroup (Fin r → K)) (hG : IsMaximalTranslationCap (KG G)) :
    IsCompleteCap (doubling (KG G)) := by sorry

end ScatCaps.Caps
