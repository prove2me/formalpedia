-- Prove2me | Theorems.Thm_RSInt_rs_Z_of_remainder
-- name    : RSInt.rs_Z_of_remainder
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:41:29.798476+00:00
-- url     : https://prove2.me/theorems/d9f2b94f-4777-462e-beb8-7fdf98e55c97
-- title:
--   Deriving the critical-line main-term bound from a remainder bound
-- statement:
--   Let $t>0$ and $C$ be real, set $a=\sqrt{t/(2\pi)}$,
--   $N=\lfloor a\rfloor_{\mathbb N}$, $p=a-N$, and
--   $\theta_{\rm main}=\frac t2\log t-\frac t2\log(2\pi)-\frac t2-\frac\pi8$.
--   Use the formal zero-division convention in
--   $\Psi(p)=\cos(2\pi(p^2-p-1/16))/\cos(2\pi p)$, and let $R(t)$ be the
--   Riemann contour remainder defined in the accompanying bundle. Define
--
--   $$Z(t,\phi)=2\sum_{n=1}^{N}n^{-1/2}\cos(\phi-t\log n)
--   +(-1)^{N+1}\left(\frac{t}{2\pi}\right)^{-1/4}\Psi(p).$$
--
--   Assume that every real $\phi$ with $|\phi-\theta_{\rm main}|\le1/t$ satisfies
--
--   $$|2\operatorname{Re}(e^{i\phi}R(t))-(-1)^{N+1}(t/(2\pi))^{-1/4}\Psi(p)|\le C.$$
--
--   Then there exist real $M>0$ and $\phi$ with $|\phi-\theta_{\rm main}|\le1/t$,
--   $\Gamma_{\mathbb R}(1/2+it)=Me^{i\phi}$, and
--
--   $$\left|\frac{\operatorname{Re}\Lambda(1/2+it)}M-Z(t,\phi)\right|\le C,$$
--
--   where $\Gamma_{\mathbb R}(s)=\pi^{-s/2}\Gamma(s/2)$ and $\Lambda$ is completed zeta.
--
--   This transfers a contour remainder estimate to a real main-term estimate.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/RS_BridgeSharp.lean#L35-L78

import Definitions.Def_ArdaRH65K_DlvpTheta
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
import Mathlib
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Theorems.Thm_RSDesignTheta_theta_sub_thetaMain
import Theorems.Thm_RSInt_completed_re_eq_rs_cos
import Theorems.Thm_ThetaConverge_convergence_obligation
import Theorems.Thm_ZeroSignDecomp_gamma_r_polar_t
/-  RS_BridgeSharp.lean -- lane RS, brick B3 part 4 SHARPENED (RSC0 Phase 2): the Riemann-Siegel
    formula for Hardy's Z with the C0 term and the SHARPENED explicit remainders of `RS_B3Sharp`,
    phase discharged hypothesis-free exactly as in `RS_Bridge` / `RSSeam_Bridge` (imports
    `RS_B3Sharp`, `RS_Bridge`; all read-only, nothing existing is edited).

    ## The headlines (no `sorry`, no `native_decide`, no new axioms)

      `RSInt.rs_Z_C0'` : for t >= 4250, 0 < p = rsFrac t, cos(2 pi p) ≠ 0, there are M > 0 and phi with
          Gammaℝ(1/2+it) = M e^{i phi},   |phi - thetaMain t| <= 1/t,   and
          | Re completedRiemannZeta(1/2+it) / M
              - ( 2 sum_{n<=N} n^(-1/2) cos(phi - t log n) + (-1)^(N+1) (t/2pi)^(-1/4) Psi(p) ) |
            <= (3/5) t^(-3/4).
      `RSSeam.rs_Z_C0_seam'` : the same for t >= 509 with (21/25) t^(-3/4).
      Same statement shape as `RSInt.rs_Z_C0` (2 t^(-3/4), t >= 10000) and `RSSeam.rs_Z_C0_seam`
      ((13/5) t^(-3/4), t >= 509); those two statements are re-derived here from the sharpened
      remainders as `RSInt.rs_Z_C0_of_sharp` and `RSSeam.rs_Z_C0_seam_of_sharp`.

    `rs_Z_of_remainder` is the proof of `RSInt.rs_Z_C0` with the remainder constant abstracted:
    any bound C on the C0-corrected remainder, valid for every phase within 1/t of thetaMain, is a
    bound on the Z formula with the island's branch-correct theta.

    conjecture1_proved = False.  An explicit finite-height formula; nothing here bears on the
    Riemann Hypothesis.
-/



open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate

noncomputable section

section
namespace RSInt
end RSInt
open RSInt

theorem RSInt.rs_Z_of_remainder {t C : ℝ} (ht0 : 0 < t)
    (hrem : ∀ φ : ℝ, |φ - rsThetaMain t| ≤ 1 / t →
      |2 * (cexp (I * φ) * rsRem t).re -
        (-1 : ℝ) ^ (rsNn t + 1) * (t / (2 * π)) ^ (-(1 / 4 : ℝ)) * rsPsi (rsFrac t)| ≤ C) :
    ∃ M φ : ℝ, 0 < M ∧ Gammaℝ ((1 / 2 : ℂ) + t * I) = (M : ℂ) * cexp (I * φ) ∧
      |φ - rsThetaMain t| ≤ 1 / t ∧
      |(completedRiemannZeta ((1 / 2 : ℂ) + t * I)).re / M -
          (2 * ∑ n ∈ Finset.Icc 1 (rsNn t), (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.cos (φ - t * Real.log n) +
            (-1 : ℝ) ^ (rsNn t + 1) * (t / (2 * π)) ^ (-(1 / 4 : ℝ)) * rsPsi (rsFrac t))| ≤ C := by sorry
