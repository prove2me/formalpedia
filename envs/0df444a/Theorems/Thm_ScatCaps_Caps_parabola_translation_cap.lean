-- Prove2me | Theorems.Thm_ScatCaps_Caps_parabola_translation_cap
-- name    : ScatCaps.Caps.parabola_translation_cap
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:05:56.558236+00:00
-- url     : https://prove2.me/theorems/94fd5966-bc48-431d-b876-cdaa7dedc30e
-- title:
--   §4, proof of Proposition 4.7, p. 21 — {(x, x²) : x ∈ 𝔽_{2^t}} is a translation cap in AG(2, 2^t)
-- statement:
--   Let $q = 2^t$. The parabola
--
--   $$\{(x, x^2) : x \in \mathbb F_{2^t}\}$$
--
--   is a translation cap in $AG(2, 2^t)$: it is a cap, and it equals $\mathcal K_G$ for an additive subgroup $G$ of $\mathbb F_{2^t}^2$.
--
--   It is the building block used, with Lemma 4.5, to raise the dimension of a maximal translation cap two coordinates at a time.
-- source:
--   Bartoli, Giulietti, Marino & Polverino, Maximum scattered linear sets and complete caps in Galois spaces, arXiv:1512.07467v1, §4, proof of Proposition 4.7, p. 21

import Mathlib
import Definitions.Def_ScatCaps_Caps_Model

namespace ScatCaps.Caps

theorem parabola_translation_cap (K : Type*) [Field K] [Fintype K] (t : ℕ)
    (hK : Fintype.card K = 2 ^ t) :
    IsTranslationCap (parabola K) := by sorry

end ScatCaps.Caps
