-- Prove2me | Theorems.Thm_ReservationPolicy_eq_10
-- name    : ReservationPolicy.eq_10
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:23:28.559711+00:00
-- url     : https://prove2.me/theorems/abc603b5-8544-4e88-bbcd-0e6cbf7f6a27
-- title:
--   Equation (10) — reward is the mean ability of admitted students
-- statement:
--   Let $\varepsilon\sim U[-1,1]$, let $m$ be the mean ability of a group and $d$ the cutoff, with $|d-m|<1$. Then the expected ability of the admitted students is
--   $$
--   E[m+\varepsilon\mid m+\varepsilon>d]=\frac{1+d+m}{2}.
--   $$
--   With $m=e$ for type $x$ and $m=\phi e$ for type $y$, this is equation (10) for the market reward.
--
--   Differences from the source:
--   - reading: (10) for every effort → the hypothesis |d − m| < 1; reason: the admitted abilities are uniform on (d, m+1) only inside the support
--   - encoding: two cases by type → one statement in the mean ability m; reason: the cases are m = e and m = ϕ e
-- source:
--   Bao, Ni & Singh, Educational Inequality and Reservation Policy in Developing Markets, SSRN 3772113 (May 30, 2023), eq. (10), p.13

import Mathlib
import Definitions.Def_ReservationPolicy_admittedMean

namespace ReservationPolicy

/-- **Equation (10).** If the cutoff `d` lies within the noise support around the mean ability `m`,
the expected ability of the admitted students is `(1 + d + m)/2`. Bao, Ni & Singh, SSRN 3772113
(May 30, 2023), eq. (10), p.13 (PDF 13). -/
theorem eq_10 (m d : ℝ) (h : |d - m| < 1) :
    admittedMean m d = (1 + d + m) / 2 := by sorry

end ReservationPolicy
