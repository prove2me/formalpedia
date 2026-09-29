-- Prove2me | Theorems.Thm_Rudin_integrals_stable
-- name    : Rudin.integrals_stable
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-14T00:35:28.721969+00:00
-- url     : https://prove2.me/theorems/5e2f181f-2379-49d0-b44e-0e68b56d9382
-- title:
--   Riemann–Stieltjes upper and lower integrals are uniformly stable
-- statement:
--   Let $\alpha$ be increasing on $[a,b]$, and suppose $f$ and $g$ differ by at most $\varepsilon\ge 0$ throughout the interval. Then both their upper and lower Riemann–Stieltjes integrals differ by at most
--
--   $$\varepsilon\bigl(\alpha(b)-\alpha(a)\bigr).$$
--
--   This lifts the partitionwise stability estimates for Darboux sums to the two extremal integrals and provides a reusable quantitative continuity principle.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd ed., proof of Theorem 7.16.

import Definitions.Def_Rudin_ch06_stieltjes
import Theorems.Thm_Rudin_sSup_image_stable
import Theorems.Thm_Rudin_sInf_image_stable
import Theorems.Thm_Rudin_exists_partition
import Theorems.Thm_Rudin_upperSum_stable
import Theorems.Thm_Rudin_lowerSum_stable

namespace Rudin

theorem integrals_stable {a b : ℝ} (hab : a ≤ b) (α f g : ℝ → ℝ)
    (hα : MonotoneOn α (Set.Icc a b)) {ε : ℝ} (hε : 0 ≤ ε)
    (hfg : ∀ x ∈ Set.Icc a b, |f x - g x| ≤ ε) :
    |upperIntegral a b f α - upperIntegral a b g α| ≤
        ε * (α b - α a) ∧
      |lowerIntegral a b f α - lowerIntegral a b g α| ≤
        ε * (α b - α a) := by sorry
