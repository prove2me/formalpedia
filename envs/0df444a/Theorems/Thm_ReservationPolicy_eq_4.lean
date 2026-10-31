-- Prove2me | Theorems.Thm_ReservationPolicy_eq_4
-- name    : ReservationPolicy.eq_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T20:22:55.90206+00:00
-- url     : https://prove2.me/theorems/b4e7bb25-7dda-4a3a-9f90-20e89d58fad4
-- title:
--   Equation (4) — admission probability under uniform noise
-- statement:
--   Let $\varepsilon\sim U[-1,1]$, let $m$ be a student's mean ability and $d$ the cutoff, with $|d-m|<1$. Then her admission probability is
--   $$
--   \Pr(m+\varepsilon>d)=\frac{1-d+m}{2}.
--   $$
--   With $m=e$ for an investing type-$x$ student and $m=\phi e$ for every other student, this is equation (4). It is the linear formula from which every closed form of the paper follows.
--
--   Differences from the source:
--   - reading: (4) for every effort → the hypothesis |d − m| < 1; reason: (4) is the uniform law's formula inside the support; outside it the probability is 0 or 1 and (4) is false
--   - encoding: three cases by type and investment → one statement in the mean ability m; reason: the cases are m = e and m = ϕ e
-- source:
--   Bao, Ni & Singh, Educational Inequality and Reservation Policy in Developing Markets, SSRN 3772113 (May 30, 2023), eq. (4), p.11

import Mathlib
import Definitions.Def_ReservationPolicy_admitProb

namespace ReservationPolicy

/-- **Equation (4).** If the cutoff `d` lies within the noise support around the mean ability `m`,
the admission probability is `(1 − d + m)/2`. Bao, Ni & Singh, SSRN 3772113 (May 30, 2023), eq. (4),
p.11 (PDF 11).

**Formalization Note** The three cases of (4) are `m = e` and `m = ϕ e`. The hypothesis `|d − m| < 1`
is the range of validity; outside it the probability is `0` or `1`. -/
theorem eq_4 (m d : ℝ) (h : |d - m| < 1) :
    admitProb m d = (1 - d + m) / 2 := by sorry

end ReservationPolicy
