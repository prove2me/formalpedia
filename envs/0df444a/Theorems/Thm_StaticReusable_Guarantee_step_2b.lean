-- Prove2me | Theorems.Thm_StaticReusable_Guarantee_step_2b
-- name    : StaticReusable.Guarantee.step_2b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:25:13.336606+00:00
-- url     : https://prove2.me/theorems/c4f9dca5-41fe-4f8b-ac7b-d1e468db05d2
-- title:
--   §3.1 Step 2b, p. 14 — for C ≥ 4, R̃(z) ≤ R(z)
-- statement:
--   Let $C \ge 4$ and $z_1, \dots, z_C \ge 0$ (with $z_{C+1} = 1$). Then
--   $$\tilde R(z_1, \dots, z_C) \le R(z_1, \dots, z_C),$$
--   where $\tilde R$ keeps only the terms $i \le 4$ of the sums in $R$ after clearing the powers of $x = \sum_{k=1}^C a_k z_{k+1}$:
--   $$\tilde R(z_1,\dots,z_C) = \frac{\left(\sum_{k=0}^{C} a_k z_{k+1}\right)\sum_{i=1}^{4} a_i u^{4-i} x^{i-1}}{\sum_{i=0}^{4} a_i u^{4-i} x^{i}}, \qquad u = \sum_{k=1}^{C} a_k z_k,\ a_i = \frac{C!}{(C-i)!}.$$
--
--   The truncation $\tilde R$ is the function Lemmas 2–4 bound from below.
-- source:
--   Besbes, Elmachtoub and Sun, Static Pricing: Universal Guarantees for Reusable Resources, arXiv:1905.00731v3, p. 14, §3.1, Step 2b (definition of R̃)

import Mathlib
import Definitions.Def_StaticReusable_Guarantee_Setting

open Finset

namespace StaticReusable.Guarantee

theorem step_2b {C : ℕ} (hC : 4 ≤ C) (z : ℕ → ℝ) (hz : ∀ k ∈ Finset.Icc 1 C, 0 ≤ z k) :
    Rt C z ≤ R C z := by sorry
end StaticReusable.Guarantee
