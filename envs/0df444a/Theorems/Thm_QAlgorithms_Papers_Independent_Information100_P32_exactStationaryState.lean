-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P32_exactStationaryState
-- name    : QAlgorithms.Papers.Independent.Information100.P32.exactStationaryState
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T10:26:21.008079+00:00
-- url     : https://prove2.me/theorems/194291de-ec5a-4c46-9552-1ac0eba81c8e
-- title:
--   Exact stationary state in the relaxing domain
-- statement:
--   Let $J,\omega\in\mathbb R$ and $\tau>0$. Each fresh, independent ancillary qubit has the same state $\rho_A=\left(\begin{smallmatrix}p_A&c_A\\c_A^*&1-p_A\end{smallmatrix}\right)$, where $0\le p_A\le1$ and $|c_A|^2\le p_A(1-p_A)$. The system and incoming ancilla are initially uncorrelated. Put $H_S=H_A=-\omega\sigma_z/2$, $H_0=H_S\otimes I+I\otimes H_A$, and $H_I=J(\sigma_x\otimes\sigma_x+\sigma_y\otimes\sigma_y)$. One collision is $\Phi(\rho)=\operatorname{Tr}_A[e^{-i\tau(H_0+H_I)}(\rho\otimes\rho_A)e^{i\tau(H_0+H_I)}]$, with no additional free interval. Units are $\hbar=k_B=1$ and $|0\rangle$ has $\sigma_z$ eigenvalue $+1$.
--
--   Write $C=\cos(2J\tau)$, $S=\sin(2J\tau)$, $L=C-\cos(\omega\tau)$, $q=|c_A|^2$, $x=2p_A-1$, $D=L^2+\sin^2(\omega\tau)$ and $K=D-4qCL$. The algebraic candidate $\rho_* =\rho(p_*,c_*)$ is constructed by
--   $$p_*=p_A+\frac{2qxCL}{K},\qquad c_*=-\frac{c_AxS}{K}\bigl(\sin(\omega\tau)+iL\bigr).$$ Assume $K>0$ and $S\ne0$. Then $\rho_*$ is a density matrix and
--   $$\Phi(\rho_*)=\rho_*,\qquad \lim_{n\to\infty}\Phi^n(\rho_0)=\rho_*$$
--   for every physical initial state $\rho_0$. Every physical fixed point equals $\rho_*$. The extra $S\ne0$ guard removes the nonrelaxing exceptional collisions missed by the source's $K>0$ condition.
-- source:
--   Coherence -assisted quantum state preparation and thermal control through repeated interactions, arXiv:2610.10794v1, PDF p. 3, §II B Eqs.(11)–(13): exact stationary solution

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P32

noncomputable section

open scoped Matrix ComplexConjugate Topology

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P32

/-- PDF pp.3–4, Eqs.(11)–(13): exact stationary state in the relaxing domain.
The additional S≠0 guard corrects the source's insufficient K>0 exclusion. -/
theorem exactStationaryState (m : Model) (hK : 0 < denominatorK m) (hS : angleS m ≠ 0) :
    IsDensityMatrix (starState m) ∧ collision m (starState m) = starState m ∧
    (∀ r, IsDensityMatrix r → collision m r = r → r = starState m) ∧
    (∀ r, IsDensityMatrix r → Tendsto (trajectory m r) atTop (𝓝 (starState m))) := by sorry

end QAlgorithms.Papers.Independent.Information100.P32

end
