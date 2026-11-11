-- Prove2me | Theorems.Thm_SparseHamiltonianNorm_Simulation_kernel_approximation
-- name    : SparseHamiltonianNorm.Simulation.kernel_approximation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:43:48.538195+00:00
-- url     : https://prove2.me/theorems/d85886f8-b826-41e3-81b6-2d139f840afb
-- title:
--   Proposition 13 — Localized phase-kernel approximation with all constants
-- statement:
--   Assume Eq. (61): $M=M^\dagger$, $V^\dagger V=I$, $t\ge0$, $\Lambda>0$, $d\ge1$, $H=2\sqrt d\,\Lambda V^\dagger MV$, $V^\dagger M^2V\preceq I/4$, $L_0\ge\max(1,\|M\|)$, and $\tau=t\sqrt d\,\Lambda$. For all positive integers $m,p$, the explicitly real kernel $\kappa_{m,p}$ is even, its absolute value is integrable, and
--   $$\int_{-\pi}^{\pi}|\kappa_{m,p}(\theta)|\,d\theta\le3,\qquad \int_{-\pi}^{\pi}\kappa_{m,p}(\theta)e^{ik\theta}\,d\theta=1\quad(k\in\mathbb Z,\ |k|\le p).$$
--   The corresponding operator integral is integrable and satisfies
--   $$\|\widetilde U_{m,p}-e^{-itH}\|_{\mathrm{op}}\le7e^{\tau/(2L_0)}(32L_0/m)^{2p}.$$
--   When $m=\lceil128L_0\rceil$, this is at most $7e^{\tau/(2L_0)}16^{-p}$. These are the complete mass, reproduction, and approximation conclusions of the source.
--
--   Differences from the source:
--   - encoding: a real signed kernel and almost-everywhere operator integral → a real-valued function, explicit integrability conclusions, and a finite-exception boundary extension; reason: reality is enforced by the formula and all source instances and constants are retained
-- source:
--   Zecheng Li, Chunhao Wang, STOC 2027 submission #1383 (October 2026), Proposition 13, p.19; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1383.pdf#page=19; printed page = PDF page; SHA256 af14a222e3d0dfd7ec18f7569a4ae416f68022ab443cdd73f9ad829fa7ec9386

import Definitions.Def_SparseHamiltonianNorm_Simulation_PhaseKernel

open scoped Matrix.Norms.L2Operator ComplexOrder

namespace SparseHamiltonianNorm.Simulation
open MeasureTheory
/-- Li--Wang, Proposition 13, p.19, Eqs. (65)--(68), including every explicit constant. -/
theorem kernel_approximation (n e d m p : ℕ) (Λ t L₀ : ℝ)
    (V : Matrix (Fin e) (Fin n) ℂ) (M : Matrix (Fin e) (Fin e) ℂ)
    (hd : 1 ≤ d) (hm : 1 ≤ m) (hp : 1 ≤ p) (hΛ : 0 < Λ) (ht : 0 ≤ t)
    (hV : V.conjTranspose * V = 1) (hM : M.IsHermitian)
    (hMoment : CompressedMoment V M) (hL : max 1 (opNorm M) ≤ L₀) :
    (∀ θ, phaseKernel m p (-θ) = phaseKernel m p θ) ∧
    Integrable (fun θ => |phaseKernel m p θ|) (volume.restrict (Set.Icc (-Real.pi) Real.pi)) ∧
    (∫ θ in Set.Icc (-Real.pi) Real.pi, |phaseKernel m p θ|) ≤ 3 ∧
    (∀ k : ℤ, |k| ≤ p →
      Integrable (fun θ => (phaseKernel m p θ : ℂ) * Complex.exp ((k : ℂ) * θ * Complex.I))
        (volume.restrict (Set.Icc (-Real.pi) Real.pi)) ∧
      (∫ θ in Set.Icc (-Real.pi) Real.pi,
        (phaseKernel m p θ : ℂ) * Complex.exp ((k : ℂ) * θ * Complex.I)) = 1) ∧
    Integrable (fun θ => phaseKernel m p θ • boundaryResponse d Λ t V M θ)
      (volume.restrict (Set.Icc (-Real.pi) Real.pi)) ∧
    opNorm (phaseIntegral d Λ t V M m p - evolution t (compressedH d Λ V M)) ≤
      7 * Real.exp (t * Real.sqrt d * Λ / (2 * L₀)) * (32 * L₀ / m) ^ (2 * p) ∧
    (m = ⌈128 * L₀⌉₊ →
      opNorm (phaseIntegral d Λ t V M m p - evolution t (compressedH d Λ V M)) ≤
        7 * Real.exp (t * Real.sqrt d * Λ / (2 * L₀)) * (16 : ℝ) ^ (-(p : ℤ))) := by sorry
end SparseHamiltonianNorm.Simulation
