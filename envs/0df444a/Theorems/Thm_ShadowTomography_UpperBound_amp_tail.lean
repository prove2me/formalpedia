-- Prove2me | Theorems.Thm_ShadowTomography_UpperBound_amp_tail
-- name    : ShadowTomography.UpperBound.amp_tail
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-07T07:25:27.54342+00:00
-- url     : https://prove2.me/theorems/da9fa433-6090-4373-bfb7-e6432c03449d
-- title:
--   Binomial tail bounds for amplified count measurements
-- statement:
--   Let $E$ be an effect and $\rho$ a density operator on $\mathcal H$, and write $p=\operatorname{Tr}(E\rho)$. For $q\ge0$, a threshold $\theta\in\mathbb R$ and a margin $\gamma>0$, consider the amplified measurements $E^{\ge\theta}_q$ and $E^{\le\theta}_q$ on $q$ registers (accept iff at least, respectively at most, $\theta q$ of the $q$ invocations of $E$ accept). On $\rho^{\otimes q}$:
--   1. if $\theta\le p-\gamma$, then $\operatorname{Tr}(E^{\ge\theta}_q\rho^{\otimes q})\ge 1-e^{-2q\gamma^2}$;
--   2. if $\theta\ge p+\gamma$, then $\operatorname{Tr}(E^{\ge\theta}_q\rho^{\otimes q})\le e^{-2q\gamma^2}$;
--   3. if $\theta\ge p+\gamma$, then $\operatorname{Tr}(E^{\le\theta}_q\rho^{\otimes q})\ge 1-e^{-2q\gamma^2}$;
--   4. if $\theta\le p-\gamma$, then $\operatorname{Tr}(E^{\le\theta}_q\rho^{\otimes q})\le e^{-2q\gamma^2}$.
--
--   On i.i.d. copies the number of accepting invocations is $\mathrm{Bin}(q,p)$, so these are Hoeffding's inequalities. They are the Chernoff-bound steps of the shadow-tomography proof (pp. 16-17), stated with a free margin so that the failure probability can be matched to the quantum union bound.
-- source:
--   S. Aaronson, Shadow Tomography of Quantum States, arXiv:1711.01053v2, https://arxiv.org/abs/1711.01053, Section 5 (proof of Theorem 2), pp. 15-19

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_ShadowTomography_UpperBound_IsEffect
import Definitions.Def_ShadowTomography_UpperBound_tensorPow
import Definitions.Def_ShadowTomography_UpperBound_POVM
import Definitions.Def_ShadowTomography_UpperBound_ampMeasurements
import Definitions.Def_ShadowTomography_UpperBound_avgMarginal
import Definitions.Def_ShadowTomography_UpperBound_seqAccept
set_option autoImplicit false

open scoped ComplexOrder MatrixOrder

namespace ShadowTomography.UpperBound

/-- **K2.** Binomial tails of the amplified count measurements (Hoeffding): with
`p = Tr(Eρ)` and margin `γ > 0`, a threshold at least `γ` below `p` makes `ampAtLeast` accept
(and `ampAtMost` reject) except with probability `exp(-2qγ²)`, and a threshold at least `γ`
above `p` makes `ampAtLeast` reject (and `ampAtMost` accept) except with that probability. -/
theorem amp_tail {n : Type} [Fintype n] [DecidableEq n] (E ρ : Matrix n n ℂ)
    (hE : IsEffect E) (hρ : WildeQIT.IsDensityOperator ρ) (q : ℕ) (θ γ : ℝ) (hγ : 0 < γ) :
    (θ ≤ (E * ρ).trace.re - γ →
      1 - Real.exp (-2 * q * γ ^ 2) ≤ (ampAtLeast E q θ * tensorPow ρ q).trace.re) ∧
    ((E * ρ).trace.re + γ ≤ θ →
      (ampAtLeast E q θ * tensorPow ρ q).trace.re ≤ Real.exp (-2 * q * γ ^ 2)) ∧
    ((E * ρ).trace.re + γ ≤ θ →
      1 - Real.exp (-2 * q * γ ^ 2) ≤ (ampAtMost E q θ * tensorPow ρ q).trace.re) ∧
    (θ ≤ (E * ρ).trace.re - γ →
      (ampAtMost E q θ * tensorPow ρ q).trace.re ≤ Real.exp (-2 * q * γ ^ 2)) := by
  sorry

end ShadowTomography.UpperBound
