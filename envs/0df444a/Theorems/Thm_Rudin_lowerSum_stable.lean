-- Prove2me | Theorems.Thm_Rudin_lowerSum_stable
-- name    : Rudin.lowerSum_stable
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-14T00:25:44.827989+00:00
-- url     : https://prove2.me/theorems/7eef3631-86c2-41fb-90d6-cf6f15fc46cd
-- title:
--   Riemann–Stieltjes lower sums are uniformly stable
-- statement:
--   Let $P$ be a partition of $[a,b]$, let $\alpha$ be increasing there, and suppose $|f-g|\le\varepsilon$ on the interval. Their lower Riemann–Stieltjes sums satisfy
--
--   $$|L(P,f,\alpha)-L(P,g,\alpha)|\le\varepsilon\bigl(\alpha(b)-\alpha(a)\bigr).$$
--
--   The bound is independent of the partition and complements the corresponding upper-sum estimate.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd ed., proof of Theorem 7.16.

import Definitions.Def_Rudin_ch06_stieltjes
import Theorems.Thm_Rudin_sInf_image_stable
import Theorems.Thm_Rudin_Partition_point_mem

namespace Rudin

theorem lowerSum_stable {a b : ℝ} (hab : a ≤ b) (α f g : ℝ → ℝ)
    (hα : MonotoneOn α (Set.Icc a b)) {ε : ℝ} (hε : 0 ≤ ε)
    (hfg : ∀ x ∈ Set.Icc a b, |f x - g x| ≤ ε)
    (P : Partition a b) :
    |lowerSum f α P - lowerSum g α P| ≤ ε * (α b - α a) := by sorry
