-- Prove2me | Theorems.Thm_RevenueOrdered_Tightness_tight_bounds_A_B
-- name    : RevenueOrdered.Tightness.tight_bounds_A_B
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:18:27.385951+00:00
-- url     : https://prove2.me/theorems/17244173-1205-4a01-a1d3-d623338c6bb7
-- title:
--   Theorem 3.4 proof, pp. 10–11 — $\mathrm{OPT}/\mathrm{RO}\to k$ and $\sum_i (r_i-r_{i-1})/r_i\to k$ as $\varepsilon\to0$
-- statement:
--   Let $k\ge1$ and consider the tight instance as a function of $\varepsilon$. As $\varepsilon\to0^+$,
--   $$
--   \frac{\mathrm{OPT}}{\mathrm{RO}}\longrightarrow k
--   \qquad\text{and}\qquad
--   \sum_{i=1}^{k}\frac{r_i-r_{i-1}}{r_i}\longrightarrow k ,
--   $$
--   where $r_0=0$. The first limit shows that Theorem 3.1 ($\mathrm{RO}\ge\mathrm{OPT}/k$) is best possible, the second that Theorem 3.2 ($\mathrm{RO}\ge\mathrm{OPT}/\sum_i (r_i-r_{i-1})/r_i$) is tight.
--
--   **Formalization Note** The limits are along the filter $\mathcal N_{>}(0)$ of right neighbourhoods of $0$; the instance is defined for every $\varepsilon$, and only small positive $\varepsilon$ matter.
-- source:
--   Berbeglia & Joret, Assortment Optimisation Under a General Discrete Choice Model: A Tight Analysis of Revenue-Ordered Assortments, arXiv:1606.01371v3, pp. 10–11, proof of Theorem 3.4

import Mathlib
import Definitions.Def_RevenueOrdered_Tightness_ChoiceModel
import Definitions.Def_RevenueOrdered_Tightness_RevenueOrdered
import Definitions.Def_RevenueOrdered_Tightness_TightInstance
open Filter Topology

namespace RevenueOrdered.Tightness

/-- Bounds (A) and (B) are tight (pp. 10–11): as `ε → 0⁺`, the ratio `OPT / RO` of the tight
instance tends to `k`, and so does `∑_{i=1}^{k} (r_i - r_{i-1}) / r_i`. -/
theorem tight_bounds_A_B (k : ℕ) [NeZero k] :
    Tendsto (fun ε : ℝ => RevenueOrdered.Ratio.opt (tightP k ε) (tightRevenue k ε) / roValue (tightP k ε) (tightRevenue k ε))
        (𝓝[>] 0) (𝓝 (k : ℝ)) ∧
      Tendsto (fun ε : ℝ => revenueGapSum (tightRevenue k ε)) (𝓝[>] 0) (𝓝 (k : ℝ)) := by sorry

end RevenueOrdered.Tightness
