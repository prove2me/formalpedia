-- Prove2me | Theorems.Thm_ThetaValue_arg_eq_arctan_of_re_pos
-- name    : ThetaValue.arg_eq_arctan_of_re_pos
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:18:20.5914+00:00
-- url     : https://prove2.me/theorems/19b66ddf-513f-4260-8be1-969dc3f43c39
-- title:
--   Argument in the right half-plane
-- statement:
--   For a complex number $w$ with $\operatorname{Re}w>0$, its principal argument satisfies
--
--   $$\operatorname{arg}w=\arctan\!\left(\frac{\operatorname{Im}w}{\operatorname{Re}w}\right).$$
--
--   This identifies the phase used in the theta-function analysis.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/ThetaValue.lean#L70-L91

import Definitions.Def_ArdaRH65K_ThetaValue
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
/-  ThetaValue.lean -- ANDÚRIL A4 θ-value instrument: toward a kernel box for
    φ(t) = arg Γℝ(1/2+it) = the Riemann–Siegel θ, with NO numeric hypotheses.

    ## THE ROUTE (Euler/Weierstrass limit form, γ-free).

    Γℝ(s) = π^{-s/2}·Γ(s/2), so with `s = 1/2+it`, `t = 14`:

        φ(14) = arg Γℝ(1/2+14i) = −7·log π + Im log Γ(1/4 + 7i).

    (Numerically φ(14) = θ_RS(14) ≈ −1.7829487; verified in the driver against mpmath's
    `siegeltheta(14)` and against `arg Γℝ` directly.)

    For `Im log Γ(z)` with `z = x+iy` (`x = 1/4`, `y = 7`) we use Mathlib's Gauss product
    `GammaSeq z n = n^z·n!/∏_{k=0}^n (z+k) → Γ(z)` (`Complex.GammaSeq_tendsto_Gamma`).  Its
    principal-log has imaginary part (this file's `imLn_formula`, PROVED):

        Im L_n = y·log n − Σ_{k=0}^n arctan(y/(x+k)),
        L_n := z·log n + log(n!) − Σ_{k=0}^n log(z+k)   (all principal complex logs),

    and `exp(L_n) = GammaSeq z n` (this file's `exp_Ln_eq_gammaSeq`, PROVED).  Each `arctan`
    term is boxed by the reusable `ArctanTaylor.arctan_bracket` instrument (no ψ, no Γ anchor).

    ## WHAT IS PROVED HERE (all axiom-clean, no numeric hypotheses).

      * `arg_eq_arctan_of_re_pos` : `w.arg = arctan(im w/re w)` for `re w > 0`  (the per-factor atom).
      * `imLn_formula`            : the exact `Im L_n` formula above, GENERAL in `(x,y,n)`, `x>0`.
      * `exp_Ln_eq_gammaSeq`      : `exp(L_n) = GammaSeq z n`, the bridge to the Gauss product.

    Together with `ArctanTaylor.arctan_bracket` these are a COMPLETE finite kernel pipeline: for
    any `n` they reduce `Im L_n` to a rational interval with no numeric hypotheses.

    ## THE PRECISE REMAINING GAP (named Props, honestly stated -- see mission "land D1 + the gap").

    Two obligations separate the proven finite `Im L_n` from the target `φ(14)` box:

      * `ThetaGap.ConvergenceObligation` (branch bridge) : `imLnVal x y n → Λ` for a real `Λ` that
        is a genuine argument of `Γ(z)` (`Γ(z) = ‖Γ(z)‖·exp(IΛ)`).  IMPORTANT honest correction,
        driver-verified: `Im L_n` converges to the CONTINUOUS unwrapped value `Im loggamma(1/4+7i)
        ≈ 6.230`, which is `arg Γ(z) + 2π` — NOT the principal `(Complex.log (Γ z)).im ≈ −0.053`.
        (`Im L_n` sweeps from `−2.93` at `n=1` up through `6.23`, crossing far outside `(−π,π)`.)  So
        the correct target is `Λ` characterized by the exp identity, not a principal-branch equality.
        This is the one genuine limit-interchange (from `exp_Ln_eq_gammaSeq` +
        `Complex.GammaSeq_tendsto_Gamma` + `exp` continuity, tracking the winding); a `Tendsto`
        obligation, NOT a numeric hypothesis.

      * `ThetaGap.RateObligation` (rate) : `|Λ − imLnVal x y n| ≤ C(x,y)/n` with an EXPLICIT
        elementary `C` -- provable by the integral-comparison harmonic-tail bound (`1/(2n)`-type
        `∑ 1/(x+k)` vs `log`) plus the cubic `arctan(u)=u−r`, `0<r<u³/3` residual, using only
        elementary calculus in Mathlib and this file's arctan corollaries.  Driver: at `n=2000`,
        honest `k≤30`, box width ≈ 9.4e-4 < the 2e-3 target.

    With both, `φ(14) = −7·log π + Λ` (continuous branch) is boxed by `−7·[log π box] +
    [imLnVal box] ± [rate]` -- a kernel interval of width ≤ 2e-3, no hypotheses.  `log π` is boxed
    by the corpus verified-log pattern, exactly as `TrigReduceOperating` boxes `log 2`.  The shape
    of the final consumption is recorded in `ThetaGap.PhiTargetShape`.

    conjecture1_proved = False.  The finite Im-part pipeline of the θ-value, kernel-clean; the θ
    VALUE box itself awaits the two named Props above (rate + branch bridge).  NOT a proof of RH.
-/




open Complex Real

section
namespace ThetaValue
end ThetaValue
open ThetaValue

/-! ### The per-factor atom: `arg` of a right-half-plane point is an `arctan`. -/

theorem ThetaValue.arg_eq_arctan_of_re_pos {w : ℂ} (hw : 0 < w.re) :
    w.arg = Real.arctan (w.im / w.re) := by sorry
