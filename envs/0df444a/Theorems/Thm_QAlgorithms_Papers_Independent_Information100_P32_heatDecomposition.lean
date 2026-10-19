-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P32_heatDecomposition
-- name    : QAlgorithms.Papers.Independent.Information100.P32.heatDecomposition
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:41:32.228256+00:00
-- url     : https://prove2.me/theorems/da256522-4f67-41a7-aa2e-dc4b76157bee
-- title:
--   Heat decomposition and zero stationary current
-- statement:
--   Let $J,\omega\in\mathbb R$ and $\tau>0$. Each fresh, independent ancillary qubit has the same state $\rho_A=\left(\begin{smallmatrix}p_A&c_A\\c_A^*&1-p_A\end{smallmatrix}\right)$, where $0\le p_A\le1$ and $|c_A|^2\le p_A(1-p_A)$. The system and incoming ancilla are initially uncorrelated. Put $H_S=H_A=-\omega\sigma_z/2$, $H_0=H_S\otimes I+I\otimes H_A$, and $H_I=J(\sigma_x\otimes\sigma_x+\sigma_y\otimes\sigma_y)$. One collision is $\Phi(\rho)=\operatorname{Tr}_A[e^{-i\tau(H_0+H_I)}(\rho\otimes\rho_A)e^{i\tau(H_0+H_I)}]$, with no additional free interval. Units are $\hbar=k_B=1$ and $|0\rangle$ has $\sigma_z$ eigenvalue $+1$.
--
--   Write $C=\cos(2J\tau)$, $S=\sin(2J\tau)$, $L=C-\cos(\omega\tau)$, $q=|c_A|^2$, $x=2p_A-1$, $D=L^2+\sin^2(\omega\tau)$ and $K=D-4qCL$. The algebraic candidate $\rho_* =\rho(p_*,c_*)$ is constructed by
--   $$p_*=p_A+\frac{2qxCL}{K},\qquad c_*=-\frac{c_AxS}{K}\bigl(\sin(\omega\tau)+iL\bigr).$$ For a physical system input $\rho=\rho(p,c)$, let $Q(\rho,a)=\operatorname{Tr}[(U^\dagger(I\otimes H_A)U-I\otimes H_A)(\rho\otimes a)]$. Split $\rho_A=a_d+a_o$, its diagonal and off-diagonal parts. Then
--   $$Q(\rho,\rho_A)=Q(\rho,a_d)+Q(\rho,a_o),$$
--   $$Q(\rho,a_d)=\omega(p_A-p)S^2,\qquad Q(\rho,a_o)=-\omega\sin(4J\tau)\operatorname{Im}(cc_A^*).$$
--   Total heat equals $-\operatorname{Tr}[H_S(\Phi(\rho)-\rho)]$. For $K>0$, $Q(\rho_*,\rho_A)=0$. Positive heat is energy entering the ancilla.
-- source:
--   Coherence -assisted quantum state preparation and thermal control through repeated interactions, arXiv:2610.10794v1, PDF p. 10, §IV Eqs.(35)–(39): heat decomposition and zero stationary current

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P32

noncomputable section

open scoped Matrix ComplexConjugate Topology

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P32

/-- PDF pp.9–10, Eqs.(35)–(39): heat components are defined through ancillary
operators, the total heat is minus the system-energy change, and stationary heat is zero. -/
theorem heatDecomposition (m : Model) (r : Op Bool) (hr : IsDensityMatrix r) :
    heat m r (rho m.pA m.cA) = heat m r (diagonalAncilla m) + heat m r (offDiagonalAncilla m) ∧
    heat m r (diagonalAncilla m) = m.frequency * (m.pA - population r) * angleS m ^ 2 ∧
    heat m r (offDiagonalAncilla m) =
      -m.frequency * Real.sin (4 * m.coupling * m.duration) * (coherence r * conj m.cA).im ∧
    heat m r (rho m.pA m.cA) =
      -((localEnergy m.frequency * (collision m r - r)).trace.re) ∧
    (0 < denominatorK m → heat m (starState m) (rho m.pA m.cA) = 0) := by sorry

end QAlgorithms.Papers.Independent.Information100.P32

end
