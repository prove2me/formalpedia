-- Prove2me | Theorems.Thm_ScatCaps_Caps_translation_cap_bound
-- name    : ScatCaps.Caps.translation_cap_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:05:55.761265+00:00
-- url     : https://prove2.me/theorems/7292cf12-3226-4d28-aa64-6676aec1fc25
-- title:
--   §4, p. 20 ([6, Prop. 2.5]) — a translation cap in AG(r, 2^t), t > 1, has at most q^{r/2} points
-- statement:
--   Let $q = 2^t$ with $t > 1$, and let $S$ be a translation cap of $AG(r, q)$. Then $|S| \le q^{r/2}$, i.e.
--
--   $$|S|^2 \le q^r .$$
--
--   This is the bound whose attainment defines maximal translation caps; in Proposition 4.7 it identifies the translation cap coming from a scattered linear set of rank $3t/2$ as maximal.
--
--   **Formalization Note** The bound is stated in the squared form to avoid the half-integer exponent $r/2$. The hypothesis $t > 1$ is necessary: for $t = 1$ all of $\mathbb F_2^r$ is a translation cap.
-- source:
--   Bartoli, Giulietti, Marino & Polverino, Maximum scattered linear sets and complete caps in Galois spaces, arXiv:1512.07467v1, §4, p. 20 (citing [6, Proposition 2.5])

import Mathlib
import Definitions.Def_ScatCaps_Caps_Model

namespace ScatCaps.Caps

theorem translation_cap_bound (K : Type*) [Field K] [Fintype K] (t : ℕ)
    (hK : Fintype.card K = 2 ^ t) (ht : 1 < t) {r : ℕ} (S : Set (Fin r → K))
    (hS : IsTranslationCap S) :
    S.ncard ^ 2 ≤ (2 ^ t) ^ r := by sorry

end ScatCaps.Caps
