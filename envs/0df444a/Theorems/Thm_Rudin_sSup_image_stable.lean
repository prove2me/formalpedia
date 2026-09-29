-- Prove2me | Theorems.Thm_Rudin_sSup_image_stable
-- name    : Rudin.sSup_image_stable
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-14T00:02:38.640341+00:00
-- url     : https://prove2.me/theorems/d2cc14f7-c87f-46a3-965a-f9623c27ba67
-- title:
--   Suprema are stable under uniform perturbations
-- statement:
--   Let $s$ be a nonempty set and let $f,g:s\to\mathbb R$ differ pointwise by at most $\varepsilon\ge 0$. Then
--
--   $$\left|\sup_{x\in s}f(x)-\sup_{x\in s}g(x)\right|\le\varepsilon.$$
--
--   The statement also covers Mathlib's totalized supremum convention for unbounded real sets. It is a reusable order-theoretic foundation for perturbation estimates of Darboux upper sums.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd ed., proof of Theorem 7.16; the extremum perturbation estimate used to compare upper Riemann–Stieltjes sums.

import Definitions.Def_Rudin_ch06_stieltjes

open Set

namespace Rudin

theorem sSup_image_stable {ι : Type*} (s : Set ι) (hs : s.Nonempty)
    (f g : ι → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hfg : ∀ x ∈ s, |f x - g x| ≤ ε) :
    |sSup (f '' s) - sSup (g '' s)| ≤ ε := by sorry
