-- Prove2me | Theorems.Thm_RS5_sampleOK_sign
-- name    : RS5.sampleOK_sign
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:46:54.049815+00:00
-- url     : https://prove2.me/theorems/fed826bf-61dc-4322-a5ac-9223248af5f8
-- title:
--   Soundness of a sample-sign certificate
-- statement:
--   Let $s$ be a sample with real height $t_s$ and stored Boolean sign $b_s$, and
--   suppose the original Boolean sample checker accepts it. For
--   $g(t)=\operatorname{Re}\Lambda(1/2+it)$, where $\Lambda$ is completed zeta,
--
--   $$b_s=\mathrm{true}\Longrightarrow g(t_s)>0,\qquad
--   b_s=\mathrm{false}\Longrightarrow g(t_s)<0.$$
--
--   This converts one accepted arithmetic sample into a strict analytic sign.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/RS5_Z.lean#L150-L163

import Definitions.Def_ArdaRH65K_DlvpTheta
import Definitions.Def_ArdaRH65K_Probes_ArbEconomics_Sound
import Definitions.Def_ArdaRH65K_RS4_Sound
import Definitions.Def_ArdaRH65K_RS5_Sound
import Definitions.Def_ArdaRH65K_RS5_Z
import Definitions.Def_ArdaRH65K_RSTheta
import Definitions.Def_ArdaRH65K_RS_B2
import Definitions.Def_ArdaRH65K_RS_B3
import Definitions.Def_ArdaRH65K_RS_C0
import Definitions.Def_ArdaRH65K_RS_Entire
import Definitions.Def_ArdaRH65K_RS_Fold
import Definitions.Def_ArdaRH65K_RS_Kernel
import Definitions.Def_ArdaRH65K_RS_Mellin
import Definitions.Def_ArdaRH65K_RS_Strip
import Definitions.Def_ArdaRH65K_ThetaConverge
import Definitions.Def_ArdaRH65K_ThetaValue
import Definitions.Def_ArdaRH65K_XiLineZeros
import Definitions.Def_ArdaRS_Arithmetic
import Definitions.Def_ArdaRS_Band
import Definitions.Def_ArdaRS_Config64
import Definitions.Def_ArdaRS_Dyadic
import Definitions.Def_ArdaRS_DyadicOps
import Definitions.Def_ArdaRS_Evaluator
import Mathlib
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic
import Mathlib.Tactic.IntervalCases
import Theorems.Thm_ArbEcon_OrderK_valid64
import Theorems.Thm_RS5_check5_sound
import Theorems.Thm_RS5_tpow_le_margin
import Theorems.Thm_RSSeam_rs_Z_C0_seam
namespace ArbEcon
end ArbEcon
namespace DIntvProd
end DIntvProd
namespace DIntvProd.DIntv
end DIntvProd.DIntv
namespace RS4
end RS4
namespace RS4.Cert
end RS4.Cert
/-  RS5_Z.lean -- lane B5: the t >= 509 checker `RS5.check5` glued to the SEAM bound
    `RSSeam.rs_Z_C0_seam` (remainder (13/5) t^(-3/4)), and certified signs of one dyadic sample.

    ## Headlines (no `sorry`, no `native_decide`, no new axioms)

      * `rs5_Z_enclosure` : `Valid c t K`, `check5 c z = true` give `M > 0`, `phi` with
            Gammaℝ(1/2+it) = M e^{i phi},  |phi - thetaMain t| <= 1/t,
            zlo/2^(2P) - (13/5) t^(-3/4) <= Re completedRiemannZeta(1/2+it) / M
                                         <= zhi/2^(2P) + (13/5) t^(-3/4)
        (the EXACT t-dependent margin of the seam bound; valid from t >= 509).
      * `tpow_le_margin` : `MarginOK c E` (an integer inequality) gives `t^(-3/4) <= E / 2^P`.
      * `rs5_Z_enclosure_E` : the same enclosure with the rational margin `(13/5) E / 2^P`.
      * `rs5_sign_pos` / `rs5_sign_neg` : a box clearing `(13/5) E / 2^P` on one side pins the SIGN of
        `Re completedRiemannZeta(1/2+it)` (= `XiLineZeros.gLine t`).
      * `sampleOK_sign` : a certified `Sample` (`sampleOK s = true`) has the claimed sign of `gLine`
        at `s.t = tn / 2^tq`.

    conjecture1_proved = False.  Finite-height sign certification; nothing about RH.
-/





open Complex
open scoped Real

section
namespace RS5
end RS5
open RS5

open ArbEcon
open RS4 (Cert Zmain)

noncomputable section















/-! ## one sample -/

theorem RS5.sampleOK_sign {s : Sample} (h : sampleOK s = true) :
    (s.pos = true → 0 < XiLineZeros.gLine s.t) ∧ (s.pos = false → XiLineZeros.gLine s.t < 0) := by sorry
