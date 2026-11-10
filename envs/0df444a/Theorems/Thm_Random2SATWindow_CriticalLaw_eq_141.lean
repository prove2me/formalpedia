-- Prove2me | Theorems.Thm_Random2SATWindow_CriticalLaw_eq_141
-- name    : Random2SATWindow.CriticalLaw.eq_141
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:42:18.313534+00:00
-- url     : https://prove2.me/theorems/b9614cf4-3dc0-47e9-aba5-ded32b1ae8cd
-- title:
--   (141) — left-tail expansions of $\pi_0,\pi_1,\pi_2$ at $x=-t$, $t\to+\infty$
-- statement:
--   As $t\to+\infty$,
--   $$\pi_0(-t)=1-\frac3{16t^3}+\frac{369}{512t^6}+O(t^{-9}),\quad\pi_1(-t)=\frac1{8t^3}-\frac{99}{128t^6}+O(t^{-9}),\quad\pi_2(-t)=\frac{35}{128t^6}+O(t^{-9}).\qquad(141)$$
--
--   Differences from the source:
--   - encoding: O(t^{−9}) as t → +∞ (three remainders) → ∃ C T0, ∀ t ≥ T0, each ‖π_q(−t) − expansion‖ ≤ C / t⁹ (one C for the three); reason: explicit form of O(·); a common constant is the maximum of three
--   - encoding: π_q(x) given by the integral (126) → piQC q x : ℂ is (126) verbatim; piQ q x = Re piQC q x, fProfile x = Σ' q, piQ q x; reason: (126) is a complex integral; Theorem 5.1(i) (theorem_5_1_i) states it is real
--   - encoding: Π with any fixed c > 0 in (30), (32) → contourPi with c = 1 (rays 1 + t e^{±iπ/3}, t > 0); reason: the paper notes the value does not depend on c > 0
-- source:
--   Ravelomanana, Inside the Critical Window of Random 2-SAT, STOC 2027 submission (manuscript sha256 eef2fa67…), §5.1.12, equation (141), printed p. 56 (PDF 58)

import Mathlib
import Definitions.Def_Random2SATWindow_CriticalLaw_Formulas
import Definitions.Def_Random2SATWindow_CriticalLaw_Airy
import Definitions.Def_Random2SATWindow_CriticalLaw_Hadamard
import Definitions.Def_Random2SATWindow_CriticalLaw_Strata
import Definitions.Def_Random2SATWindow_CriticalLaw_Saddle
import Definitions.Def_Random2SATWindow_CriticalLaw_PureLiteral

set_option autoImplicit false

open Filter Topology MeasureTheory

namespace Random2SATWindow.CriticalLaw

/-- **(141)** (left-tail expansions of the first three strata, §5.1.12, printed p. 56 / PDF 58):
as `t → +∞`,
`π_0(-t) = 1 - 3/(16t³) + 369/(512t⁶) + O(t^{-9})`, `π_1(-t) = 1/(8t³) - 99/(128t⁶) + O(t^{-9})`,
`π_2(-t) = 35/(128t⁶) + O(t^{-9})`. -/
theorem eq_141 :
    ∃ C T0 : ℝ, ∀ t : ℝ, T0 ≤ t →
      ‖piQC 0 (-t) - ((1 - 3 / (16 * t ^ 3) + 369 / (512 * t ^ 6) : ℝ) : ℂ)‖ ≤ C / t ^ 9 ∧
      ‖piQC 1 (-t) - ((1 / (8 * t ^ 3) - 99 / (128 * t ^ 6) : ℝ) : ℂ)‖ ≤ C / t ^ 9 ∧
      ‖piQC 2 (-t) - ((35 / (128 * t ^ 6) : ℝ) : ℂ)‖ ≤ C / t ^ 9 := by sorry

end Random2SATWindow.CriticalLaw
