-- Prove2me | Theorems.Thm_ScatCaps_Caps_proposition_4_3
-- name    : ScatCaps.Caps.proposition_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:05:47.64593+00:00
-- url     : https://prove2.me/theorems/bbc22f44-f011-4c25-8582-7105a4ad1885
-- title:
--   Proposition 4.3, p. 19 — scattered 𝔽₂-linear sets of PG(r − 1, 2^t) correspond to translation caps of AG(r, 2^t)
-- statement:
--   Let $t > 1$, $V = \mathbb F_{2^t}^r$, and let $U$ be an $\mathbb F_2$-subspace of $V$. Then
--
--   $$L_U \text{ is a scattered } \mathbb F_2\text{-linear set of } PG(r-1, 2^t) \iff \mathcal K_U \text{ is a translation cap of } AG(r, 2^t).$$
--
--   Since every translation cap is $\mathcal K_U$ for an additive subgroup (= $\mathbb F_2$-subspace) $U$, this gives the bijection $L_U \mapsto \mathcal K_U$ between scattered $\mathbb F_2$-linear sets and translation caps described after the proposition.
--
--   **Formalization Note** $U$ is a set with the $\mathbb F_2$-subspace property, $\mathbb F_2$ being the prime subfield of $K = \mathbb F_{2^t}$; scattered-ness is taken with respect to the points $\langle u\rangle_{\mathbb F_{2^t}}$ (the subfield $K$ itself). $\mathcal K_U$ is the set $U$ of points.
-- source:
--   Bartoli, Giulietti, Marino & Polverino, Maximum scattered linear sets and complete caps in Galois spaces, arXiv:1512.07467v1, p. 19, Proposition 4.3

import Mathlib
import Definitions.Def_ScatCaps_Caps_Model
import Definitions.Def_ScatCaps_LinearSets_Model

namespace ScatCaps.Caps

theorem proposition_4_3 (K : Type*) [Field K] [Fintype K] (t : ℕ)
    (hK : Fintype.card K = 2 ^ t) (ht : 1 < t) {r : ℕ} (U : Set (Fin r → K))
    (hU : ScatCaps.LinearSets.IsFqSubspace (⊥ : Subfield K) U) :
    ScatCaps.LinearSets.IsScattered (⊥ : Subfield K) (⊤ : Subfield K) U ↔ IsTranslationCap U := by sorry

end ScatCaps.Caps
