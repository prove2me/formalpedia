-- Prove2me | Theorems.Thm_RSSeam_rs_Z_C0_seam
-- name    : RSSeam.rs_Z_C0_seam
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-28T06:42:00.081199+00:00
-- url     : https://prove2.me/theorems/635381f5-40d3-469c-8773-485259e04604
-- title:
--   Certified Riemann–Siegel main-term error above height 509
-- statement:
--   Let $t\ge509$, $a=\sqrt{t/(2\pi)}$, $N=\lfloor a\rfloor_{\mathbb N}$,
--   and $p=a-N>0$ with $\cos(2\pi p)\ne0$. Define
--   $\theta_{\rm main}=\frac t2\log t-\frac t2\log(2\pi)-\frac t2-\frac\pi8$ and
--
--   $$Z(t,\phi)=2\sum_{n=1}^{N}n^{-1/2}\cos(\phi-t\log n)
--   +(-1)^{N+1}\left(\frac{t}{2\pi}\right)^{-1/4}
--   \frac{\cos(2\pi(p^2-p-1/16))}{\cos(2\pi p)}.$$
--
--   There exist real $M>0$ and $\phi$ such that
--   $\Gamma_{\mathbb R}(1/2+it)=Me^{i\phi}$,
--   $|\phi-\theta_{\rm main}|\le1/t$, and
--
--   $$\left|\frac{\operatorname{Re}\Lambda(1/2+it)}M-Z(t,\phi)\right|
--   \le\frac{13}{5}t^{-3/4},$$
--
--   where $\Gamma_{\mathbb R}(s)=\pi^{-s/2}\Gamma(s/2)$ and $\Lambda$ is completed zeta.
--
--   This is the analytic error envelope for the lower-height sign checker.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_reflection/lean/RSSeam_Bridge.lean#L34-L81

import Definitions.Def_ArdaRH65K_DlvpTheta
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
import Theorems.Thm_RSSeam_rs_remainder_C0_alpha_seam
import Theorems.Thm_ThetaConverge_convergence_obligation
import Theorems.Thm_ZeroSignDecomp_gamma_r_polar_t
namespace RSInt
end RSInt
/-  RSSeam_Bridge.lean -- lane SEAM: the Riemann-Siegel formula for Hardy's Z with the C0 term and an
    explicit remainder from t >= 509, phase discharged HYPOTHESIS-FREE exactly as in `RS_Bridge`
    (imports `RSSeam_B3Bound`, `RS_Bridge`, the island's `RSTheta` and `ZeroSignDecomp_t14`;
    all read-only).

    ## The headline (no `sorry`, no `native_decide`, no new axioms)

      `rs_Z_C0_seam` : for t >= 509, 0 < p = rsFrac t, cos(2 pi p) ≠ 0, there are M > 0 and phi with
          Gammaℝ(1/2+it) = M e^{i phi},   |phi - thetaMain t| <= 1/t,   and
          | Re completedRiemannZeta(1/2+it) / M
              - ( 2 sum_{n<=N} n^(-1/2) cos(phi - t log n) + (-1)^(N+1) (t/2pi)^(-1/4) Psi(p) ) |
            <= (13/5) t^(-3/4),
      N = floor(sqrt(t/2pi)), p = sqrt(t/2pi) - N, Psi(p) = cos(2 pi (p^2 - p - 1/16)) / cos(2 pi p).

    This is `RSInt.rs_Z_C0` with the range lowered from t >= 10000 to t >= 509 (constant 2 -> 13/5),
    so the Riemann-Siegel range now overlaps the Euler-Maclaurin kernel ladder (which reaches 1000 on
    this branch and 8000 via `AND.ladder_h8000_kernel`).

    conjecture1_proved = False.  An explicit finite-height formula; nothing here bears on the
    Riemann Hypothesis.
-/



open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate

noncomputable section

section
namespace RSSeam
end RSSeam
open RSSeam

open RSInt

theorem RSSeam.rs_Z_C0_seam {t : ℝ} (ht : 509 ≤ t) (hp : 0 < rsFrac t)
    (hcos : Real.cos (2 * π * rsFrac t) ≠ 0) :
    ∃ M φ : ℝ, 0 < M ∧ Gammaℝ ((1 / 2 : ℂ) + t * I) = (M : ℂ) * cexp (I * φ) ∧
      |φ - rsThetaMain t| ≤ 1 / t ∧
      |(completedRiemannZeta ((1 / 2 : ℂ) + t * I)).re / M -
          (2 * ∑ n ∈ Finset.Icc 1 (rsNn t), (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.cos (φ - t * Real.log n) +
            (-1 : ℝ) ^ (rsNn t + 1) * (t / (2 * π)) ^ (-(1 / 4 : ℝ)) * rsPsi (rsFrac t))| ≤
        13 / 5 * t ^ (-(3 / 4 : ℝ)) := by sorry
