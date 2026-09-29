-- Prove2me | Theorems.Thm_RamareAnalytic_harmonic_floor_error_le
-- name    : RamareAnalytic.harmonic_floor_error_le
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-19T19:45:00.854756+00:00
-- url     : https://prove2.me/theorems/d78a0b00-1390-4efd-a5c6-1b3792b65d72
-- title:
--   A uniform fractional-power bound for the harmonic remainder
-- statement:
--   Let $H_n=\sum_{k=1}^n 1/k$ for $n\ge 1$, with $H_0=0$, and let $\gamma$ be the Euler–Mascheroni constant. For every positive real number $t$,
--
--   $$
--   \left|H_{\lfloor t\rfloor}-\log t-\gamma\right|
--   \le \frac45\,t^{-2/5}.
--   $$
--
--   The estimate includes noninteger arguments and the range $0<t<1$, where the harmonic sum vanishes. A uniform bound on this full domain is useful when harmonic sums occur at rescaled arguments in a Dirichlet-convolution estimate, and when extending a finite convolution to a convergent infinite series.
--
--   This explicit choice of exponent and constant is an auxiliary estimate for the Ramaré squarefree-totient sum formalization. It is derived here from classical harmonic-number bounds; it is not claimed to be the optimal constant or a formula transcribed from Ramaré's paper. It supplies one analytic input, without asserting the required coefficient moments or the final squarefree-totient bound.
-- source:
--   Auxiliary estimate derived in this formal development for the harmonic-convolution method of O. Ramaré, On Shnirelman's constant, Ann. Scuola Norm. Sup. Pisa 22 (1995), 645–706, Lemmas 3.2–3.3, printed pp. 656–658; https://www.numdam.org/item/ASNSP_1995_4_22_4_645_0/ . The exponent 2/5 and constant 4/5 are chosen here, not transcribed from that source. Classical input: Mathlib NumberTheory/Harmonic/EulerMascheroni.lean, revision 0df444a360eaa60ab8c11dca51a86af692955474, eulerMascheroniSeq_lt_eulerMascheroniConstant and eulerMascheroniConstant_lt_eulerMascheroniSeq'. Intended large-range consumer: https://prove2.me/theorems/017351d0-907f-4262-b614-6850111f1ff0 .

import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option autoImplicit false

theorem RamareAnalytic.harmonic_floor_error_le (t : ℝ) (ht : 0 < t) :
    |(harmonic ⌊t⌋₊ : ℝ) - Real.log t - Real.eulerMascheroniConstant| ≤
      (4 / 5 : ℝ) * t ^ (-(2 / 5 : ℝ)) := by sorry
