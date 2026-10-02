-- Prove2me | Theorems.Thm_TeschlQM_Dynamics_wiener
-- name    : TeschlQM.Dynamics.wiener
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T06:55:47.321339+00:00
-- url     : https://prove2.me/theorems/7e939076-742a-446d-9570-cdc9f6a0c167
-- title:
--   Theorem 5.4 (Wiener) — Cesàro mean of |μ̂(t)|² is the sum of squared atoms
-- statement:
--   Let $\mu$ be a finite complex Borel measure on $\mathbb R$ and let $\hat\mu(t) = \int_{\mathbb R} \mathrm e^{-\mathrm it\lambda}\, d\mu(\lambda)$ be its Fourier transform. Then the Cesàro time average of $|\hat\mu(t)|^2$ has the limit
--   $$\lim_{T\to\infty} \frac1T \int_0^T |\hat\mu(t)|^2\, dt = \sum_{\lambda\in\mathbb R} |\mu(\{\lambda\})|^2,$$
--   where the sum on the right-hand side is finite.
--
--   Applied to the spectral measures $\mu_{\varphi,\psi}$ of a self-adjoint operator, it shows that the time-averaged transition probability $|\langle\varphi, \mathrm e^{-\mathrm itA}\psi\rangle|^2$ is controlled by the atoms of the spectral measure, and is the starting point for the RAGE theorem.
--
--   **Formalization Note.** The sum over the uncountable index set $\mathbb R$ is an unconditional sum (`tsum`), and its finiteness is part of the conclusion (`Summable`). $\hat\mu$ is `measureFourier`.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 126, Theorem 5.4, Eqs. (5.8)–(5.9)

import Mathlib
import Definitions.Def_TeschlQM_Dynamics_measureFourier

open MeasureTheory Filter Topology

namespace TeschlQM.Dynamics

/-- Teschl, Theorem 5.4 (Wiener), p. 126, (5.8)–(5.9): for a finite complex Borel measure `μ` on
`ℝ` with Fourier transform `μ̂(t) = ∫_ℝ e^{−itλ} dμ(λ)`, the Cesàro time average of `|μ̂(t)|²`
has the limit `lim_{T→∞} (1/T) ∫₀ᵀ |μ̂(t)|² dt = ∑_{λ∈ℝ} |μ({λ})|²`, where the sum on the
right-hand side (over the uncountable index set `ℝ`, with only countably many nonzero terms) is
finite. -/
theorem wiener (μ : ComplexMeasure ℝ) :
    Summable (fun x : ℝ => ‖μ {x}‖ ^ 2) ∧
    Tendsto (fun T : ℝ => (1 / T) * ∫ t in (0 : ℝ)..T, ‖measureFourier μ t‖ ^ 2) atTop
      (𝓝 (∑' x : ℝ, ‖μ {x}‖ ^ 2)) := by sorry

end TeschlQM.Dynamics
