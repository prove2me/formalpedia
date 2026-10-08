-- Prove2me | Theorems.Thm_RhinViola_lemma3NumeratorRecurrence
-- name    : RhinViola.lemma3NumeratorRecurrence
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T00:11:35.837123+00:00
-- url     : https://prove2.me/theorems/884acaab-24af-48b7-990b-0474391ffd28
-- title:
--   Algebraic numerator recurrence underlying Rhin-Viola Lemma 3
-- statement:
--   For u=1-x, v=1-y and q=1-xy, the identity uv=u+v-q gives u^(k+1)v^(l+1) = -u^k v^l q + u^(k+1)v^l + u^k v^(l+1). This is the pointwise algebraic recurrence used in the proof of Rhin and Viola's Lemma 3 before dividing by a power of q and integrating.
-- source:
--   G. Rhin and C. Viola, On the irrationality measure of zeta(2), Annales de l'Institut Fourier 43 (1993), Lemma 3, p. 90.

import Mathlib.Tactic

theorem RhinViola.lemma3NumeratorRecurrence
    (k l : ℕ) (x y : ℝ) :
    (1 - x) ^ (k + 1) * (1 - y) ^ (l + 1) =
      -((1 - x) ^ k * (1 - y) ^ l) * (1 - x * y) +
        (1 - x) ^ (k + 1) * (1 - y) ^ l +
        (1 - x) ^ k * (1 - y) ^ (l + 1) := by sorry
