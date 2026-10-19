-- Prove2me | Theorems.Thm_StaticReusable_Guarantee_lemma_3
-- name    : StaticReusable.Guarantee.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:25:39.739346+00:00
-- url     : https://prove2.me/theorems/be64e585-7c10-49cb-a858-be775fa6dc10
-- title:
--   Lemma 3, p. 15 — R̃(0, z_2, …, z_C) ≥ 104/131
-- statement:
--   Let $C \ge 4$. For all $z_2, \dots, z_C \ge 0$ (with $z_{C+1} = 1$),
--   $$\tilde R(0, z_2, \dots, z_C) \ge \frac{104}{131}.$$
--
--   This is the uniform lower bound in the case $y \ge a_1 z_1$, after Lemma 2 has moved $z_1$ to $0$.
--
--   **Formalization Note** The vector $z$ is a function on $\mathbb N$; its first coordinate is overwritten by $0$ (`Function.update z 1 0`), so only $z_2, \dots, z_C$ are constrained.
-- source:
--   Besbes, Elmachtoub and Sun, Static Pricing: Universal Guarantees for Reusable Resources, arXiv:1905.00731v3, p. 15, Lemma 3

import Mathlib
import Definitions.Def_StaticReusable_Guarantee_Setting

open Finset

namespace StaticReusable.Guarantee

theorem lemma_3 {C : ℕ} (hC : 4 ≤ C) (z : ℕ → ℝ) (hz : ∀ k ∈ Finset.Icc 2 C, 0 ≤ z k) :
    (104 / 131 : ℝ) ≤ Rt C (Function.update z 1 0) := by sorry
end StaticReusable.Guarantee
