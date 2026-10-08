-- Prove2me | Theorems.Thm_TalagrandConc_BinPacking_prop_6_4
-- name    : TalagrandConc.BinPacking.prop_6_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:43:34.847549+00:00
-- url     : https://prove2.me/theorems/93b8db36-f06b-46ec-b173-c50402a99688
-- title:
--   Proposition 6.4 — P(B_N ≤ a) P(B_N ≥ a + 4t√N (E X₁²)^{1/2} + 1) ≤ e^{−t²/4} + e^{−2N E X₁²}
-- statement:
--   Let $\mu$ be a probability measure on $[0,1]$, $P = \mu^{\otimes N}$ the product probability on $[0,1]^N$, $\mathbb E X_1^2 = \int \omega^2\,d\mu(\omega)$, and $B_N$ the bin packing number. Then for all $t > 0$ and all $a > 0$,
--   $$P\big(B_N(x) \le a\big)\; P\big(B_N(x) \ge a + 4t\sqrt N\,(\mathbb E X_1^2)^{1/2} + 1\big) \le e^{-t^2/4} + e^{-2N\,\mathbb E X_1^2}. \tag{6.4}$$
--
--   This "basic inequality" bounds the product of a lower and an upper tail probability of $B_N$; choosing $a$ to be a median, or a median shifted down, gives two-sided concentration.
-- source:
--   Talagrand, Concentration of measure and isoperimetric inequalities in product spaces, Publ. Math. IHÉS 81 (1995), p. 152, Proposition 6.4, Eq. (6.4)

import Mathlib
import Definitions.Def_TalagrandConc_BinPacking_Basic

namespace TalagrandConc.BinPacking

open MeasureTheory

/-- Talagrand (1995), p. 152, Proposition 6.4, Eq. (6.4): for all `t > 0` and `a > 0`,
`P(B_N ≤ a) · P(B_N ≥ a + 4t √N (E X₁²)^{1/2} + 1) ≤ e^{−t²/4} + e^{−2N E X₁²}`. -/
theorem prop_6_4 (μ : Measure unitInterval) [IsProbabilityMeasure μ] (N : ℕ)
    (t : ℝ) (ht : 0 < t) (a : ℝ) (ha : 0 < a) :
    Measure.pi (fun _ : Fin N => μ) {x | (binNumber x : ℝ) ≤ a} *
        Measure.pi (fun _ : Fin N => μ)
          {x | a + 4 * t * Real.sqrt N * Real.sqrt (secondMoment μ) + 1 ≤ (binNumber x : ℝ)} ≤
      ENNReal.ofReal (Real.exp (-(t ^ 2 / 4)) + Real.exp (-(2 * N * secondMoment μ))) := by sorry

end TalagrandConc.BinPacking
