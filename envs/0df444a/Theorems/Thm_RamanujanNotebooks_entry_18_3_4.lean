-- Prove2me | Theorems.Thm_RamanujanNotebooks_entry_18_3_4
-- name    : RamanujanNotebooks.entry_18_3_4
-- status  : Open
-- author  : @Xiang Huang
-- created : 2026-10-07T04:06:06.164025+00:00
-- url     : https://prove2.me/theorems/a7b1c7d1-b14a-4851-9105-76705fc49b96
-- title:
--   Order of accuracy of Ramanujan's second approximation to the perimeter of an ellipse
-- statement:
--   Ramanujan's approximation $L\approx\pi(a+b)\{1+3t/(10+\sqrt{4-3t})\}$, $t=((a-b)/(a+b))^2$, agrees with $L/(\pi(a+b))={}_2F_1(-\tfrac12,-\tfrac12;1;t)$ through the term $t^4$, the error being about $3t^5/2^{17}$. Stated: $\lim_{t\to0^+}\big({}_2F_1(-\tfrac12,-\tfrac12;1;t)-1-3t/(10+\sqrt{4-3t})\big)/t^5=3/2^{17}$.
-- source:
--   Bruce C. Berndt, Ramanujan's Notebooks, Part III (Springer, 1991), Chapter 18, Entry 3, (3.4), p. 146, eq. (3.4).

import Mathlib
import Definitions.Def_RamanujanNotebooks_shared_hyp2F1R
import Definitions.Def_RamanujanNotebooks_shared_shiftedFactorialR

namespace RamanujanNotebooks
theorem entry_18_3_4 :
    Filter.Tendsto
      (fun t : ℝ =>
        (hyp2F1R (-1 / 2) (-1 / 2) 1 t - (1 + 3 * t / (10 + Real.sqrt (4 - 3 * t)))) / t ^ 5)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (3 / 2 ^ 17)) := by sorry
end RamanujanNotebooks
