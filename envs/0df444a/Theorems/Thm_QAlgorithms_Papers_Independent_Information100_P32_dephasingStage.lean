-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P32_dephasingStage
-- name    : QAlgorithms.Papers.Independent.Information100.P32.dephasingStage
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T10:39:37.527987+00:00
-- url     : https://prove2.me/theorems/53c082ff-f724-4c15-8eac-baed4b973e02
-- title:
--   Ising collisions erase coherence while retaining populations
-- statement:
--   Let $J,\omega\in\mathbb R$ and $\tau>0$. Each fresh, independent ancillary qubit has the same state $\rho_A=\left(\begin{smallmatrix}p_A&c_A\\c_A^*&1-p_A\end{smallmatrix}\right)$, where $0\le p_A\le1$ and $|c_A|^2\le p_A(1-p_A)$. The system and incoming ancilla are initially uncorrelated. Put $H_S=H_A=-\omega\sigma_z/2$, $H_0=H_S\otimes I+I\otimes H_A$, and $H_I=J(\sigma_x\otimes\sigma_x+\sigma_y\otimes\sigma_y)$. One collision is $\Phi(\rho)=\operatorname{Tr}_A[e^{-i\tau(H_0+H_I)}(\rho\otimes\rho_A)e^{i\tau(H_0+H_I)}]$, with no additional free interval. Units are $\hbar=k_B=1$ and $|0\rangle$ has $\sigma_z$ eigenvalue $+1$. Replace the flip-flop interaction in the second stage by $J_{zz}\sigma_z\otimes\sigma_z$, retaining $H_0$ and fresh copies of the same ancilla. For an arbitrary initial system density matrix $\rho_0=\rho(p_0,c_0)$, write
--   $$\eta=p_Ae^{-i(2J_{zz}-\omega)\tau}+(1-p_A)e^{i(2J_{zz}+\omega)\tau}.$$
--   If $0<p_A<1$ and $\sin(2J_{zz}\tau)\ne0$, then for every $n\ge0$,
--   $$\Phi_Z^n(\rho_0)=\rho(p_0,c_0\eta^n),\quad |\eta|^2=1-4p_A(1-p_A)\sin^2(2J_{zz}\tau)<1,$$
--   and $\Phi_Z^n(\rho_0)\to\rho(p_0,0)$. With $\omega>0$ and $0<p_0<1$, the limit is a genuine Gibbs state at the temperature set by these unchanged populations.
-- source:
--   Coherence -assisted quantum state preparation and thermal control through repeated interactions, arXiv:2610.10794v1, PDF p. 8, §III C Eqs.(27)–(30): dephasing stage produces target thermal populations

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P32

noncomputable section

open scoped Matrix ComplexConjugate Topology

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P32

/-- PDF p.8, Eqs.(27)–(30): every population is preserved, n starts at zero,
and the coherence vanishes under the stated strict contraction conditions. -/
theorem dephasingStage (m : Model) (jzz : ℝ) (r : Op Bool) (hr : IsDensityMatrix r)
    (hp : 0 < m.pA) (hp1 : m.pA < 1) (hS : Real.sin (2 * jzz * m.duration) ≠ 0) :
    (∀ n : ℕ, (dephasingCollision m jzz)^[n] r =
      rho (population r) (coherence r * dephasingFactor m jzz ^ n)) ∧
    Complex.normSq (dephasingFactor m jzz) =
      1 - 4 * m.pA * (1 - m.pA) * Real.sin (2 * jzz * m.duration) ^ 2 ∧
    Complex.normSq (dephasingFactor m jzz) < 1 ∧
    Tendsto (fun n : ℕ => (dephasingCollision m jzz)^[n] r) atTop
      (𝓝 (rho (population r) 0)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P32

end
