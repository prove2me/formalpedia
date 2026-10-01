-- Prove2me | Theorems.Thm_VeinottWagnerSS_Bounds_critical_numbers_exist
-- name    : VeinottWagnerSS.Bounds.critical_numbers_exist
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-29T13:38:07.016743+00:00
-- url     : https://prove2.me/theorems/67c098fe-a269-4744-8cd3-8c71c849aea2
-- title:
--   §4, pp. 537–538 — the parameters $\bar{S}$, $\underline{s}$, $\bar{s}$ of (21)–(23) exist
-- statement:
--   Let $G_\alpha : \mathbb Z \to \mathbb R$ be convex on the integers with $G_\alpha(y) \to \infty$ as $|y| \to \infty$, let $K \ge 0$ and $0 \le \alpha \le 1$, and let $\underline{S}$ be the smallest minimizer of $G_\alpha$. Then:
--
--   1. $\bar{S}$ is the least integer $y$ with $y \ge \underline{S}$ and $G_\alpha(y+1) \ge G_\alpha(\underline{S}) + \alpha K$;
--   2. $\underline{s}$ is the least integer $y$ with $G_\alpha(y) \le G_\alpha(\underline{S}) + K$;
--   3. $\bar{s}$ is the least integer $y$ with $G_\alpha(y) \le G_\alpha(\underline{S}) + (1-\alpha) K$.
--
--   In particular each of the three sets is nonempty and has a least element, as the paper asserts ("The existence of the above parameters is ensured by the fact that $\lim_{|y|\to\infty} G_\alpha(y) = \infty$").
--
--   This guarantees that the bounds $\bar S$, $\underline s$, $\bar s$ used in Theorem 4 are well defined.
--
--   **Formalization Note** "Least element" is Mathlib's `IsLeast`: membership in the set plus being a lower bound of it. `SHigh G K α`, `sLow G K` and `sHigh G K α` are defined as infima of these sets.
-- source:
--   Veinott & Wagner, Computing Optimal (s, S) Inventory Policies, Management Sci. 11 (1965), pp. 537-538, Section 4 'Bounds on s* and S*', Eqs. (21)-(23) and the sentence following them

import Mathlib
import Definitions.Def_VeinottWagnerSS_Bounds_CriticalNumbers

namespace VeinottWagnerSS.Bounds

/-- pp. 537–538: under the standing assumptions, the parameters of (21)–(23) exist:
`S̄ = SHigh G K α` is the smallest integer `y ≥ S̲` with `G_α(y + 1) ≥ G_α(S̲) + αK` (21),
`s̲ = sLow G K` is the smallest integer `y` with `G_α(y) ≤ G_α(S̲) + K` (22), and
`s̄ = sHigh G K α` is the smallest integer `y` with `G_α(y) ≤ G_α(S̲) + (1 − α)K` (23). -/
theorem critical_numbers_exist (G : ℤ → ℝ) (K α : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) (hK : 0 ≤ K)
    (hconv : ∀ y : ℤ, G (y + 1) - G y ≤ G (y + 2) - G (y + 1))
    (hG_top : Filter.Tendsto G Filter.atTop Filter.atTop)
    (hG_bot : Filter.Tendsto G Filter.atBot Filter.atTop) :
    IsLeast {y : ℤ | SLow G ≤ y ∧ G (SLow G) + α * K ≤ G (y + 1)} (SHigh G K α) ∧
      IsLeast {y : ℤ | G y ≤ G (SLow G) + K} (sLow G K) ∧
      IsLeast {y : ℤ | G y ≤ G (SLow G) + (1 - α) * K} (sHigh G K α) := by sorry

end VeinottWagnerSS.Bounds
