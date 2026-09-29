-- Prove2me | Theorems.Thm_Rudin_sInf_image_stable
-- name    : Rudin.sInf_image_stable
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-14T00:02:38.364485+00:00
-- url     : https://prove2.me/theorems/99aaa582-06fd-4bbd-9167-c75280613b12
-- title:
--   Infima are stable under uniform perturbations
-- statement:
--   Let $s$ be a nonempty set and let $f,g:s\to\mathbb R$ differ pointwise by at most $\varepsilon\ge 0$. Then
--
--   $$\left|\inf_{x\in s}f(x)-\inf_{x\in s}g(x)\right|\le\varepsilon.$$
--
--   The statement also covers Mathlib's totalized infimum convention for unbounded real sets. It is the lower-sum counterpart of supremum stability.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd ed., proof of Theorem 7.16; the extremum perturbation estimate used to compare lower Riemann–Stieltjes sums.

import Definitions.Def_Rudin_ch06_stieltjes

open Set

namespace Rudin

theorem sInf_image_stable {ι : Type*} (s : Set ι) (hs : s.Nonempty)
    (f g : ι → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hfg : ∀ x ∈ s, |f x - g x| ≤ ε) :
    |sInf (f '' s) - sInf (g '' s)| ≤ ε := by sorry
