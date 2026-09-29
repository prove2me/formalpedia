-- Prove2me | Theorems.Thm_Rudin_ch06_abs_integral_le_of_bounded
-- name    : Rudin.ch06_abs_integral_le_of_bounded
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-14T05:33:44.318144+00:00
-- url     : https://prove2.me/theorems/54694917-3690-4e42-bbe0-bbe90897e850
-- title:
--   Bound for the Riemann-Stieltjes integral (Rudin 6.12 d)
-- statement:
--   **A bound for the Riemann–Stieltjes integral.** Let $\alpha$ be monotonically increasing on $[a,b]$ and suppose $|f(x)| \le M$ for every $x \in [a,b]$. Then
--   $$\left|\int_a^b f\,d\alpha\right| \;\le\; M\,\bigl(\alpha(b) - \alpha(a)\bigr).$$
--
--   This is part (d) of Rudin's Theorem 6.12, isolated as a standalone lemma. Every upper sum satisfies the bound: on each subinterval the supremum of $f$ lies in $[-M, M]$, the increments $\Delta\alpha_i$ are nonnegative, and they telescope to $\alpha(b) - \alpha(a)$. The bound then passes to the infimum over partitions, the set of upper sums being nonempty (it contains the value at the trivial partition $a \le b$) and bounded below.
--
--   **Formalization note.** Integrability of $f$ is not assumed: the bound holds for the upper integral of any bounded function, which is how `Rudin.RSIntegral` is defined. Boundedness, on the other hand, is essential — `sSup` returns $0$ on sets unbounded above, so an unbounded $f$ can produce upper sums with no relation to any $M$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd ed., Chapter 6, Theorem 6.12(d), p. 129.

import Mathlib
import Definitions.Def_Rudin_ch06_stieltjes

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 6.12(d): if `|f| ≤ M` on `[a, b]` then the Riemann-Stieltjes integral is
bounded by `M (α b - α a)`. -/
theorem ch06_abs_integral_le_of_bounded (a b : ℝ) (hab : a ≤ b) (f α : ℝ → ℝ)
    (hα : MonotoneOn α (Set.Icc a b)) (M : ℝ) (hM : ∀ x ∈ Set.Icc a b, |f x| ≤ M) :
    |RSIntegral a b f α| ≤ M * (α b - α a) := by sorry

end Rudin
