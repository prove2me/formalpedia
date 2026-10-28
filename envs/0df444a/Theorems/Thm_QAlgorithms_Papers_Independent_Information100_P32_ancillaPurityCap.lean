-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P32_ancillaPurityCap
-- name    : QAlgorithms.Papers.Independent.Information100.P32.ancillaPurityCap
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T10:24:38.763576+00:00
-- url     : https://prove2.me/theorems/d9790881-bbd3-4b70-990f-701ddeb38d39
-- title:
--   Stationary purity is capped by ancilla purity
-- statement:
--   Let $J,\omega\in\mathbb R$ and $\tau>0$. Each fresh, independent ancillary qubit has the same state $\rho_A=\left(\begin{smallmatrix}p_A&c_A\\c_A^*&1-p_A\end{smallmatrix}\right)$, where $0\le p_A\le1$ and $|c_A|^2\le p_A(1-p_A)$. The system and incoming ancilla are initially uncorrelated. Put $H_S=H_A=-\omega\sigma_z/2$, $H_0=H_S\otimes I+I\otimes H_A$, and $H_I=J(\sigma_x\otimes\sigma_x+\sigma_y\otimes\sigma_y)$. One collision is $\Phi(\rho)=\operatorname{Tr}_A[e^{-i\tau(H_0+H_I)}(\rho\otimes\rho_A)e^{i\tau(H_0+H_I)}]$, with no additional free interval. Units are $\hbar=k_B=1$ and $|0\rangle$ has $\sigma_z$ eigenvalue $+1$.
--
--   Write $C=\cos(2J\tau)$, $S=\sin(2J\tau)$, $L=C-\cos(\omega\tau)$, $q=|c_A|^2$, $x=2p_A-1$, $D=L^2+\sin^2(\omega\tau)$ and $K=D-4qCL$. The algebraic candidate $\rho_* =\rho(p_*,c_*)$ is constructed by
--   $$p_*=p_A+\frac{2qxCL}{K},\qquad c_*=-\frac{c_AxS}{K}\bigl(\sin(\omega\tau)+iL\bigr).$$ For $K>0$, with $\mathcal P(\rho)=\operatorname{Tr}(\rho^2)$,
--   $$\mathcal P(\rho_*)\le\mathcal P(\rho_A),\qquad \mathcal P(\rho_*)=\mathcal P(\rho_A)\ \Longleftrightarrow\ c_A=0.$$
--   This is a cap on the constructed stationary candidate, not on arbitrary transient states.
-- source:
--   Coherence -assisted quantum state preparation and thermal control through repeated interactions, arXiv:2610.10794v1, PDF p. 19, Abstract; §III B Eq.(26); Appendix D: ancilla purity cap

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P32

noncomputable section

open scoped Matrix ComplexConjugate Topology

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P32

/-- PDF pp.1,7,19–20, Eq.(26), Appendix D: the stationary candidate cannot exceed
ancilla purity. D3's missing x is corrected using D6–D7; the PDF D5 bracket is correct. -/
theorem ancillaPurityCap (m : Model) (hK : 0 < denominatorK m) :
    purity (starState m) ≤ purity (rho m.pA m.cA) ∧
    (purity (starState m) = purity (rho m.pA m.cA) ↔ m.cA = 0) := by sorry

end QAlgorithms.Papers.Independent.Information100.P32

end
