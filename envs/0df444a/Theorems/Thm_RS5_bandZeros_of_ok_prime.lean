-- Prove2me | Theorems.Thm_RS5_bandZeros_of_ok_prime
-- name    : RS5.bandZeros_of_ok_prime
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:51:30.933643+00:00
-- url     : https://prove2.me/theorems/41d66f9c-6622-405c-a12d-ee2369add552
-- title:
--   Critical-line zero list from an accepted sharp band certificate
-- statement:
--   Let $s_0,\ldots,s_m$ be a nonempty finite list of samples, with real heights
--   $t_0,\ldots,t_m$ and stored Boolean signs. Suppose the sharp Boolean band
--   checker accepts this list, and let $K$ be its number of adjacent sign changes.
--   Then there are strictly increasing real numbers $r_1,\ldots,r_K$ such that
--
--   $$t_0<r_j<t_m,\qquad
--   \Lambda(1/2+ir_j)=\zeta(1/2+ir_j)=0\quad(1\le j\le K),$$
--
--   where $\Lambda$ is completed zeta. The list of zeros is empty when $K=0$.
--
--   This turns an accepted sharp band of integer checks into a list of distinct critical-line zeros.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/RS5_BandSharp.lean#L52-L54

import Definitions.Def_ArdaRH65K_DlvpTheta
import Definitions.Def_ArdaRH65K_Probes_ArbEconomics_Sound
import Definitions.Def_ArdaRH65K_RS4_Sound
import Definitions.Def_ArdaRH65K_RS5_Band
import Definitions.Def_ArdaRH65K_RS5_Sound
import Definitions.Def_ArdaRH65K_RS5_Z
import Definitions.Def_ArdaRH65K_RSTheta
import Definitions.Def_ArdaRH65K_RS_B2
import Definitions.Def_ArdaRH65K_RS_B3
import Definitions.Def_ArdaRH65K_RS_B3Sharp
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
import Definitions.Def_ArdaRS_BandSharp
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
import Theorems.Thm_RS5_chain_zeros
import Theorems.Thm_RS5_sampleOK_prime_sign
namespace XiLineZeros
end XiLineZeros
/-  RS5_BandSharp.lean -- lane B5, RSC0 Phase 3: the band certificate over the SHARPENED predicate
    `RS5.bandOK'` (margin (3/5) t^(-3/4), every sample at t >= 4250).  Theorems BESIDE `RS5_Band`
    (imported read-only; the generic `chain_zeros`, `ltH_real`, `BandZeros` and its gluing are reused).

    ## Headlines (no `sorry`, no `native_decide`, no new axioms)

      * `band_sound'` : `bandOK' (s0 :: rest) = true` gives a strictly increasing list of
        `chgBy Sample.pos (s0 :: rest)` on-line zeros of `riemannZeta` strictly inside
        `(s0.t, (lastOf s0 rest).t)` -- the same conclusion as `band_sound`;
      * `bandZeros_of_ok'` : the same as `BandZeros`, so sharpened chunks glue with old ones
        (`BandZeros.glue`).

    conjecture1_proved = False.  Finitely many certified zeros; nothing about RH.
-/



open Complex

section
namespace RS5
end RS5
open RS5

noncomputable section

theorem RS5.bandZeros_of_ok_prime (s0 : Sample) (rest : List Sample) (h : bandOK' (s0 :: rest) = true) :
    BandZeros s0.t (lastOf s0 rest).t (chgBy Sample.pos (s0 :: rest)) := by sorry
