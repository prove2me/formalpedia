-- Prove2me | Theorems.Thm_ScatCaps_Caps_theorem_4_2
-- name    : ScatCaps.Caps.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:06:11.858547+00:00
-- url     : https://prove2.me/theorems/cbd2abc2-f9d0-405e-8b51-ea1af83cc223
-- title:
--   Theorem 4.2, p. 19 — 𝒦_G is a translation cap iff distinct non-zero vectors of G are 𝔽_q-linearly independent (q even)
-- statement:
--   Let $q = 2^t$ and let $G$ be an additive subgroup of $\mathbb F_q^r$. Then
--
--   $$\mathcal K_G \text{ is a translation cap of } AG(r,q) \iff \text{any two non-zero distinct } u, v \in G \text{ are } \mathbb F_q\text{-linearly independent.}$$
--
--   This characterizes translation caps purely in terms of the group $G$; it is the bridge between caps and scattered linear sets (Proposition 4.3).
--
--   **Formalization Note** "$q$ even" is the hypothesis $|K| = 2^t$. Linear independence of $u, v$ is Mathlib's `LinearIndependent K ![u, v]`.
-- source:
--   Bartoli, Giulietti, Marino & Polverino, Maximum scattered linear sets and complete caps in Galois spaces, arXiv:1512.07467v1, p. 19, Theorem 4.2 (citing [6, Lemma 2.1])

import Mathlib
import Definitions.Def_ScatCaps_Caps_Model

namespace ScatCaps.Caps

theorem theorem_4_2 (K : Type*) [Field K] [Fintype K] (t : ℕ)
    (hK : Fintype.card K = 2 ^ t) {r : ℕ} (G : AddSubgroup (Fin r → K)) :
    IsTranslationCap (KG G) ↔
      ∀ u ∈ G, ∀ v ∈ G, u ≠ 0 → v ≠ 0 → u ≠ v → LinearIndependent K ![u, v] := by sorry

end ScatCaps.Caps
