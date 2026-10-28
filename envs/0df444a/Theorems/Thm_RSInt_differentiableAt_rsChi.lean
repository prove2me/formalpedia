-- Prove2me | Theorems.Thm_RSInt_differentiableAt_rsChi
-- name    : RSInt.differentiableAt_rsChi
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T05:51:34.710754+00:00
-- url     : https://prove2.me/theorems/ce2e1c4e-b5c2-4b9d-a4ff-9a345a920f45
-- title:
--   Differentiability of the zeta reflection factor
-- statement:
--   Define $\chi(s)=\pi^{s-1/2}\Gamma((1-s)/2)/\Gamma(s/2)$ using the complex-power
--   and reciprocal conventions of the accompanying definitions. If $s\in\mathbb C$
--   is not any positive odd integer, then
--
--   $$\chi\text{ is complex differentiable at }s.$$
--
--   This regularity is used in the Riemann–Siegel integral identity.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/RS_Entire.lean#L282-L294

import Definitions.Def_ArdaRH65K_RS_Entire
import Definitions.Def_ArdaRH65K_RS_Fold
import Definitions.Def_ArdaRH65K_RS_Kernel
import Definitions.Def_ArdaRH65K_RS_Mellin
import Definitions.Def_ArdaRH65K_RS_Strip
import Mathlib
/-  RS_Entire.lean -- lane RS, ANDURIL brick B2 (the Riemann-Siegel integral), part 5:
    holomorphy in `s` of the two Riemann-Siegel line integrals, and the chi factor.
    Mathlib-only (imports `RS_Fold`).

    ## Contents (no `sorry`, no `native_decide`, no new axioms)

      * `differentiable_integral_cpow` : a generic parametric-holomorphy lemma:
            s |-> int W(v) X(v)^s dv   is entire
        for continuous W with a Gaussian tail and a continuous line X in the slit plane with
        m <= |X v| <= alpha + beta |v|.
      * `differentiable_rsA`, `differentiable_rsB` : s |-> lineUp c (rsG x^(-s)) and
        s |-> lineDn c (rsH x^(s-1)) are entire for every c > 0 that is not an integer.
      * `rsChi s = pi^(s - 1/2) Gamma((1-s)/2) / Gamma(s/2)`, holomorphic off {1, 3, 5, ...}
        (`differentiableAt_rsChi`), with the Gamma-function identity
            rsChi s * Gamma s * (2 cos(pi s / 2)) = (2 pi)^s     (Re s > 0)
        (`rsChi_mul_Gamma_cos`, reflection + duplication).

    conjecture1_proved = False.
-/


open Complex MeasureTheory Filter Topology Set
open scoped Real

noncomputable section

section
namespace RSInt
end RSInt
open RSInt

/-! ## 1. A generic parametric-holomorphy lemma -/







/-! ## 2. The two Riemann-Siegel line integrals are entire in `s` -/



















/-! ## 3. The chi factor -/

theorem RSInt.differentiableAt_rsChi {s : ℂ} (hs : ∀ k : ℕ, s ≠ 2 * k + 1) :
    DifferentiableAt ℂ rsChi s := by sorry
