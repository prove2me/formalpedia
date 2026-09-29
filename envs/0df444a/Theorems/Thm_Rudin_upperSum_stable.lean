-- Prove2me | Theorems.Thm_Rudin_upperSum_stable
-- name    : Rudin.upperSum_stable
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-14T00:25:42.080271+00:00
-- url     : https://prove2.me/theorems/3ff2dacf-6084-4644-8007-81648d41eeeb
-- title:
--   Riemann–Stieltjes upper sums are uniformly stable
-- statement:
--   Let $P$ be a partition of $[a,b]$, let $\alpha$ be increasing there, and suppose $|f-g|\le\varepsilon$ on the interval. Their upper Riemann–Stieltjes sums satisfy
--
--   $$|U(P,f,\alpha)-U(P,g,\alpha)|\le\varepsilon\bigl(\alpha(b)-\alpha(a)\bigr).$$
--
--   The bound is independent of the partition and is the quantitative upper-sum estimate behind uniform-limit theorems for the Riemann–Stieltjes integral.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd ed., proof of Theorem 7.16.

import Definitions.Def_Rudin_ch06_stieltjes
import Theorems.Thm_Rudin_sSup_image_stable
import Theorems.Thm_Rudin_Partition_point_mem

namespace Rudin

theorem upperSum_stable {a b : ℝ} (hab : a ≤ b) (α f g : ℝ → ℝ)
    (hα : MonotoneOn α (Set.Icc a b)) {ε : ℝ} (hε : 0 ≤ ε)
    (hfg : ∀ x ∈ Set.Icc a b, |f x - g x| ≤ ε)
    (P : Partition a b) :
    |upperSum f α P - upperSum g α P| ≤ ε * (α b - α a) := by sorry
