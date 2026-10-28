-- Prove2me | Theorems.Thm_RSInt_continuousAt_rsH_cpow_zero
-- name    : RSInt.continuousAt_rsH_cpow_zero
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T05:51:48.806477+00:00
-- url     : https://prove2.me/theorems/6275e7bc-ae55-41fc-9c14-7511bc8da4ea
-- title:
--   Continuity of the lower kernel times a power at zero
-- statement:
--   Let $D(z)=e^{\pi iz}-e^{-\pi iz}$ and $H(z)=e^{-\pi iz^2}/D(z)$, using the
--   complex division and principal-power conventions of the definitions. If
--   $s\in\mathbb C$ has $\operatorname{Re}s>2$, then
--
--   $$z\longmapsto H(z)z^{s-1}\text{ is continuous at }z=0.$$
--
--   This regularity is used when shifting a contour through the origin.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/RS_Fold.lean#L64-L108

import Definitions.Def_ArdaRH65K_RS_Fold
import Definitions.Def_ArdaRH65K_RS_Kernel
import Definitions.Def_ArdaRH65K_RS_Mellin
import Definitions.Def_ArdaRH65K_RS_Strip
import Mathlib
import Theorems.Thm_RSInt_deriv_rsD_int_ne_zero
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

theorem RSInt.continuousAt_rsH_cpow_zero {s : ℂ} (hs : 2 < s.re) :
    ContinuousAt (fun x => rsH x * x ^ (s - 1)) 0 := by sorry
