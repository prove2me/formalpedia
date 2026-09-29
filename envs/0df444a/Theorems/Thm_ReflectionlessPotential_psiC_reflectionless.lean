-- Prove2me | Theorems.Thm_ReflectionlessPotential_psiC_reflectionless
-- name    : ReflectionlessPotential.psiC_reflectionless
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T19:49:07.013978+00:00
-- url     : https://prove2.me/theorems/6662f40d-f1f6-4a1a-8694-b203f5636c48
-- title:
--   Reflectionlessness: $\psi_k$ is asymptotically a pure transmitted wave
-- statement:
--   End of §2 of the paper: the potential is **reflectionless**.
--
--   For $\kappa>0$ and real $k$, the continuum state $\psi_{k}(x) = e^{ikx}(k+i\kappa\tanh\kappa x)/\bigl(\sqrt{2\pi}(\kappa+ik)\bigr)$ behaves as
--   $$\psi_{k}(x) \;\longrightarrow\; \frac{k-i\kappa}{\sqrt{2\pi}\,(\kappa+ik)}\;e^{ikx}
--   \quad (x\to-\infty),
--   \qquad
--   \psi_{k}(x) \;\longrightarrow\; \frac{k+i\kappa}{\sqrt{2\pi}\,(\kappa+ik)}\;e^{ikx}
--   \quad (x\to+\infty),$$
--   in the sense that the difference of $\psi_k$ and the displayed pure wave tends to $0$. On both sides the asymptotic wave is a *right-moving* $e^{ikx}$ only: no reflected $e^{-ikx}$ component appears, so the reflection amplitude vanishes, $R(k)=0$. The two amplitudes have equal modulus $1/\sqrt{2\pi}$, i.e. the transmission probability is one at every energy.
-- source:
--   F. Erman, O. T. Turgut, "Completeness of Energy Eigenfunctions for the Reflectionless Potential in Quantum Mechanics", arXiv:2411.14941v1

import Mathlib
import Definitions.Def_ReflectionlessPotentialDefs

open Complex MeasureTheory Filter Topology

namespace ReflectionlessPotential

theorem psiC_reflectionless (κ k : ℝ) (hκ : 0 < κ) :
    Tendsto (fun x : ℝ => psiC κ k x -
        Complex.exp (Complex.I * k * x) * (((k : ℂ) - Complex.I * κ) /
          ((Real.sqrt (2 * Real.pi) : ℂ) * ((κ : ℂ) + Complex.I * k)))) atBot (𝓝 0) ∧
      Tendsto (fun x : ℝ => psiC κ k x -
        Complex.exp (Complex.I * k * x) * (((k : ℂ) + Complex.I * κ) /
          ((Real.sqrt (2 * Real.pi) : ℂ) * ((κ : ℂ) + Complex.I * k)))) atTop (𝓝 0) ∧
      ‖((k : ℂ) - Complex.I * κ) / ((Real.sqrt (2 * Real.pi) : ℂ) * ((κ : ℂ) + Complex.I * k))‖ =
        ‖((k : ℂ) + Complex.I * κ) /
          ((Real.sqrt (2 * Real.pi) : ℂ) * ((κ : ℂ) + Complex.I * k))‖ := by sorry

end ReflectionlessPotential
