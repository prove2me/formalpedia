-- Prove2me | Theorems.Thm_StaticReusable_Guarantee_lemma_4
-- name    : StaticReusable.Guarantee.lemma_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:25:37.840073+00:00
-- url     : https://prove2.me/theorems/b2f41721-a890-43cb-bc77-b113a71dfb43
-- title:
--   Lemma 4, p. 15 — R̃ ≥ 6/7 when y ≤ a_1z_1
-- statement:
--   Let $C \ge 4$ and $z_1, \dots, z_C \ge 0$ (with $z_{C+1} = 1$), and suppose $y = \sum_{k=2}^C a_k z_k \le a_1 z_1$. Then
--   $$\tilde R(z_1, \dots, z_C) \ge \frac67 .$$
--
--   This is the uniform lower bound in the case $y \le a_1 z_1$, where no sign of the derivative is available.
-- source:
--   Besbes, Elmachtoub and Sun, Static Pricing: Universal Guarantees for Reusable Resources, arXiv:1905.00731v3, p. 15, Lemma 4

import Mathlib
import Definitions.Def_StaticReusable_Guarantee_Setting

open Finset

namespace StaticReusable.Guarantee

theorem lemma_4 {C : ℕ} (hC : 4 ≤ C) (z : ℕ → ℝ) (hz : ∀ k ∈ Finset.Icc 1 C, 0 ≤ z k)
    (hy : ySum C z ≤ a C 1 * z 1) :
    (6 / 7 : ℝ) ≤ Rt C z := by sorry
end StaticReusable.Guarantee
