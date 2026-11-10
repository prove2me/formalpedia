-- Prove2me | Theorems.Thm_Random2SATWindow_CriticalLaw_eq_144_145
-- name    : Random2SATWindow.CriticalLaw.eq_144_145
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:42:29.171117+00:00
-- url     : https://prove2.me/theorems/0e082a77-1d16-40bc-86b7-9de14b825a09
-- title:
--   (144)–(145) — right tail of $\pi_0$ by the residue at $a'_1$: $\pi_0(x)=C_0e^{-x^3/6+a'_1x/2}(1+O(e^{-\varepsilon x}))$, $C_0>0$
-- statement:
--   Let $a'_1>a'_2>\cdots$ be the negative zeros of $\mathrm{Ai}'$ and fix $d_*$ with $a'_2<d_*<a'_1$. Then, as $x\to+\infty$,
--   $$\pi_0(x)=C_0e^{-x^3/6+a'_1x/2}\big(1+O(e^{-\varepsilon x})\big),\qquad\varepsilon=\frac{a'_1-d_*}2>0,\qquad(144)$$
--   where $C_0=\sqrt{\pi/2}\,\dfrac{A_{1/2}(2^{-2/3}a'_1)}{-a'_1\mathrm{Ai}(a'_1)}$ (145), and $C_0>0$.
--
--   In Lean $a'_1,a'_2$ enter as hypotheses: $a'_2<a'_1<0$ are zeros of $A_1=-\mathrm{Ai}'$, and $A_1$ has no other real zero above $a'_2$.
--
--   Differences from the source:
--   - encoding: a'_1 > a'_2, the two largest (negative) zeros of Ai′ → hypotheses a2 < a1 < 0, A_1(a1) = A_1(a2) = 0, and A_1(y) ≠ 0 for real y > a2, y ≠ a1; reason: A_1 = −Ai′ by (31); these conditions single out the two largest real zeros, which exist (a'_1 ≈ −1.019, a'_2 ≈ −3.248)
--   - encoding: Ai(a'_1) in (145) → airyA 0 a1; reason: A_0 = Ai by (31)
--   - encoding: 1 + O(e^{−εx}) as x → +∞; C_0 > 0 → ∃ K X0, ∀ x ≥ X0, ∃ E, ‖E‖ ≤ K e^{−εx} ∧ π_0(x) = C_0 e^{…}(1 + E); (C_0).im = 0 ∧ 0 < (C_0).re; reason: explicit form of O(·); C_0 is computed in ℂ
--   - encoding: π_q(x) given by the integral (126) → piQC q x : ℂ is (126) verbatim; piQ q x = Re piQC q x, fProfile x = Σ' q, piQ q x; reason: (126) is a complex integral; Theorem 5.1(i) (theorem_5_1_i) states it is real
--   - encoding: Π with any fixed c > 0 in (30), (32) → contourPi with c = 1 (rays 1 + t e^{±iπ/3}, t > 0); reason: the paper notes the value does not depend on c > 0
-- source:
--   Ravelomanana, Inside the Critical Window of Random 2-SAT, STOC 2027 submission (manuscript sha256 eef2fa67…), §5.1.13, equations (144)–(145), printed p. 57 (PDF 59); positivity of C_0 via (146), printed p. 58 (PDF 60)

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

/-- **(144)–(145)** (right tail of the zeroth stratum, §5.1.13, printed p. 57 / PDF 59). Let
`a'_1 > a'_2` be the two largest zeros of `Ai′ = -A_1` (they are negative) and
`a'_2 < d_* < a'_1`. Then, as `x → +∞`,
`π_0(x) = C_0 e^{-x³/6 + a'_1 x/2} (1 + O(e^{-εx}))`, `ε = (a'_1 - d_*)/2 > 0`, with
`C_0 = √(π/2) A_{1/2}(2^{-2/3} a'_1) / (-a'_1 Ai(a'_1))` (145), and `C_0 > 0`. -/
theorem eq_144_145 (a1 a2 : ℝ) (h21 : a2 < a1) (ha1 : a1 < 0)
    (hz1 : airyA 1 a1 = 0) (hz2 : airyA 1 a2 = 0)
    (hzero : ∀ y : ℝ, a2 < y → y ≠ a1 → airyA 1 y ≠ 0)
    (d : ℝ) (hd2 : a2 < d) (hd1 : d < a1) :
    (∃ K X0 : ℝ, ∀ x : ℝ, X0 ≤ x → ∃ E : ℂ, ‖E‖ ≤ K * Real.exp (-((a1 - d) / 2) * x) ∧
      piQC 0 x = rightTailConst a1 * (Real.exp (-x ^ 3 / 6 + a1 * x / 2) : ℂ) * (1 + E)) ∧
    (rightTailConst a1).im = 0 ∧ 0 < (rightTailConst a1).re := by sorry

end Random2SATWindow.CriticalLaw
