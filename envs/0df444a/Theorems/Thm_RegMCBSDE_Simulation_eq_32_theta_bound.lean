-- Prove2me | Theorems.Thm_RegMCBSDE_Simulation_eq_32_theta_bound
-- name    : RegMCBSDE.Simulation.eq_32_theta_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T06:38:42.12603+00:00
-- url     : https://prove2.me/theorems/2a12f6a1-3ea4-4fad-90f4-1017de9bce4d
-- title:
--   Proof of Theorem 3, Step 2, Eq. (32) — |θ^{i,I,M}_k|² ≤ C(𝒜^{N,M}_{k+1} + h ℬ^{N,M}_k) on A^M_k
-- statement:
--   Under the standing assumptions of Section 5, let $\alpha^{i,I,M}_k$ be the empirical regression scheme (4), $\theta^{i,I,M}_k$ its rescaling, and set (p. 18)
--   $$\mathcal A^{N,M}_k=\frac1M\sum_{m=1}^M|\rho^N_{0,k}(P^{N,m}_{t_k})|^2,\qquad \mathcal B^{N,M}_k=\frac1M\sum_{m=1}^M|f^m_k(0,\dots,0)|^2 .$$
--   There are constants $C>0$ and $h_0>0$ such that, for $h<h_0$, every $i\ge0$ and every $0\le k\le N-1$,
--   $$|\theta^{i,I,M}_k|^2\le C\big(\mathcal A^{N,M}_{k+1}+h\,\mathcal B^{N,M}_k\big)\qquad\text{on }\mathbf A^M_k. \qquad (32)$$
--
--   This pathwise bound on the empirical coefficients is the step of the proof of Theorem 3 that controls the size of the fitted coefficients, in terms of the truncation levels at the next time and the driver at zero.
--
--   **Formalization Note** The paper defines $\rho^N_{0,k}$ only for $k\le N-1$; at $k=N-1$ the quantity $\mathcal A^{N,M}_N$ is read as $\frac1M\sum_m|\Phi^N(P^{N,m}_{t_N})|^2$, the mean squared response of the regression at the last step. $C$ and $h_0$ depend only on the model; the bound holds for every $C_0$, every truncation profile $\xi$ and every $I$.
-- source:
--   Gobet, Lemor and Warin, A regression-based Monte Carlo method to solve backward stochastic differential equations, arXiv:math/0508491v1, p. 20, Proof of Theorem 3, Step 2, Eq. (32) (with 𝒜, ℬ defined on p. 18)

import Mathlib
import Definitions.Def_RegMCBSDE_Simulation_Setting
import Definitions.Def_RegMCBSDE_Simulation_ProjectionScheme
import Definitions.Def_RegMCBSDE_Simulation_EmpiricalScheme

namespace RegMCBSDE.Simulation

open MeasureTheory ProbabilityTheory

/-- Proof of Theorem 3, Step 2, Eq. (32), p. 20: for `h` small enough, on `𝐀^M_k`,
`|θ^{i,I,M}_k|² ≤ C (𝒜^{N,M}_{k+1} + h ℬ^{N,M}_k)` for every `i ≥ 0` and `k ≤ N-1`, where
`𝒜^{N,M}_{k+1} = (1/M) ∑_m |ρ^N_{0,k+1}(P^{N,m}_{t_{k+1}})|²` and
`ℬ^{N,M}_k = (1/M) ∑_m |f^m_k(0, …, 0)|²` (p. 18).

Pinned reading: `ρ^N_{0,N}` is not defined by the paper; at `k = N-1`, `𝒜^{N,M}_N` is read as
`(1/M) ∑_m |Φ^N(P^{N,m}_{t_N})|²`, the mean squared response. `C` and `h₀` depend only on the
model; the bound holds for every `C₀` and every truncation profile `ξ`. -/
theorem eq_32_theta_bound {d q : ℕ} (m : Model d q) (hm : m.Standing) :
    ∃ C > 0, ∃ h₀ > 0, ∀ (d' : ℕ) (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (D : RefData d q d' Ω) (B : Basis q d'),
      m.h D.N < h₀ → D.IsAdmissible m P → B.IsOrthonormal D P →
      ∀ (M : ℕ), 1 ≤ M → ∀ (ΔWs : Fin M → ℕ → Ω → E q) (PNs : Fin M → ℕ → Ω → E d'),
      IsSimulation D P M ΔWs PNs →
      ∀ (ξ : ℝ → ℝ), IsTruncationFn ξ → ∀ (C0 : ℝ) (I : ℕ) (αM : ℕ → (k : ℕ) → Ω → Coeff B k),
      IsEmpiricalScheme m D B C0 ξ ΔWs PNs I αM →
      ∀ k < D.N, ∀ ω ∈ goodEvent m D B ΔWs PNs k, ∀ i,
        let 𝒜 : ℝ := if k + 1 < D.N then (1 / (M : ℝ)) * ∑ s : Fin M, rho B C0 0 (k + 1) (PNs s (k + 1) ω) ^ 2
          else (1 / (M : ℝ)) * ∑ s : Fin M, D.ΦN (PNs s D.N ω) ^ 2
        let ℬ : ℝ := (1 / (M : ℝ)) * ∑ s : Fin M, drv m (D.withPath (ΔWs s) (PNs s)) B k 0 ω ^ 2
        sqn (theta m D B (αM i k ω)) ≤ C * (𝒜 + m.h D.N * ℬ) := by sorry

end RegMCBSDE.Simulation
