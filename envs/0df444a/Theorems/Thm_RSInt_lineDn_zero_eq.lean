-- Prove2me | Theorems.Thm_RSInt_lineDn_zero_eq
-- name    : RSInt.lineDn_zero_eq
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:13:30.097136+00:00
-- url     : https://prove2.me/theorems/b0ba30c8-8c0e-4f5a-b6d4-4757b3c33c64
-- title:
--   Shifting the lower contour away from zero
-- statement:
--   Let $\operatorname{Re}s>2$ and $0<c<1$. Define
--   $D(z)=e^{\pi iz}-e^{-\pi iz}$, $H(z)=e^{-\pi iz^2}/D(z)$, and
--   $L_-(c,F)=\int_{\mathbb R}F(c+v(1-i))(1-i)\,dv$. Then
--
--   $$L_-(0,z\mapsto H(z)z^{s-1})=L_-(c,z\mapsto H(z)z^{s-1}),$$
--
--   using principal complex powers and the accompanying conventions at zero.
--
--   This moves the lower contour into the first gap between denominator zeros.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/RS_Fold.lean#L206-L239

import Definitions.Def_ArdaRH65K_RS_Fold
import Definitions.Def_ArdaRH65K_RS_Kernel
import Definitions.Def_ArdaRH65K_RS_Mellin
import Definitions.Def_ArdaRH65K_RS_Strip
import Mathlib
import Theorems.Thm_RSInt_continuousAt_rsH_cpow_zero
import Theorems.Thm_RSInt_integrable_of_continuous_of_tail
import Theorems.Thm_RSInt_lineDn_eq_of_strip
import Theorems.Thm_RSInt_norm_rsH_mul_le
/-  RS_Fold.lean -- lane RS, ANDURIL brick B2 (the Riemann-Siegel integral), part 4:
    the chi-side line.  Mathlib-only (imports `RS_Mellin`).

    ## Contents (no `sorry`, no `native_decide`, no new axioms)

      * `norm_cpow_le_exp` : ‖x^w‖ <= e^{pi |Im w|} e^{Re w ‖x‖} for Re w >= 0 (growth of x^w).
      * `continuousAt_rsH_cpow_zero` : for Re s > 2 the chi-side integrand rsH(x) x^(s-1) is
        continuous at the pole x = 0 of rsH (removable via dslope, value 0).
      * `lineDn_zero_fold` : FOLDING.  For Re s > 2 the chi-side integral along the line through 0
        is (1 + e^{i pi s}) times the half-line integral:
            lineDn 0 (rsH x^(s-1)) = (1 + e^{i pi s}) rsHR s
        (rsH is odd, and (-x)^(s-1) = x^(s-1) e^{i pi (s-1)} on that line).
      * `lineDn_zero_eq` : the line through 0 may be moved to any c in (0, 1) (strip Cauchy; the
        pole at 0 sits on the boundary and is harmless for Re s > 2).
      * `lineDn_eq_fold` : lineDn c (rsH x^(s-1)) = (1 + e^{i pi s}) rsHR s, 0 < c < 1, Re s > 2.

    conjecture1_proved = False.
-/


open Complex MeasureTheory Filter Topology Set
open scoped Real

noncomputable section

section
namespace RSInt
end RSInt
open RSInt

/-! ## 1. Growth of `x^w` -/



/-! ## 2. Continuity of the chi-side integrand at 0 -/





/-! ## 3. Folding the line through 0 -/

















/-! ## 4. Moving the chi-side line off the pole -/

theorem RSInt.lineDn_zero_eq {s : ℂ} (hs : 2 < s.re) {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    lineDn 0 (fun x => rsH x * x ^ (s - 1)) = lineDn c (fun x => rsH x * x ^ (s - 1)) := by sorry
