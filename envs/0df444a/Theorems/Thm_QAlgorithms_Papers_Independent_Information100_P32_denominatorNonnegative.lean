-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P32_denominatorNonnegative
-- name    : QAlgorithms.Papers.Independent.Information100.P32.denominatorNonnegative
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:47:11.292989+00:00
-- url     : https://prove2.me/theorems/f6171482-b296-486c-9d2a-b86a8c3d5668
-- title:
--   The stationary denominator is nonnegative
-- statement:
--   Let $J,\omega\in\mathbb R$ and $\tau>0$. Each fresh, independent ancillary qubit has the same state $\rho_A=\left(\begin{smallmatrix}p_A&c_A\\c_A^*&1-p_A\end{smallmatrix}\right)$, where $0\le p_A\le1$ and $|c_A|^2\le p_A(1-p_A)$. The system and incoming ancilla are initially uncorrelated. Put $H_S=H_A=-\omega\sigma_z/2$, $H_0=H_S\otimes I+I\otimes H_A$, and $H_I=J(\sigma_x\otimes\sigma_x+\sigma_y\otimes\sigma_y)$. One collision is $\Phi(\rho)=\operatorname{Tr}_A[e^{-i\tau(H_0+H_I)}(\rho\otimes\rho_A)e^{i\tau(H_0+H_I)}]$, with no additional free interval. Units are $\hbar=k_B=1$ and $|0\rangle$ has $\sigma_z$ eigenvalue $+1$.
--
--   Write $C=\cos(2J\tau)$, $S=\sin(2J\tau)$, $L=C-\cos(\omega\tau)$, $q=|c_A|^2$, $x=2p_A-1$, $D=L^2+\sin^2(\omega\tau)$ and $K=D-4qCL$. The algebraic candidate $\rho_* =\rho(p_*,c_*)$ is constructed by
--   $$p_*=p_A+\frac{2qxCL}{K},\qquad c_*=-\frac{c_AxS}{K}\bigl(\sin(\omega\tau)+iL\bigr).$$
--   $$K\ge0.$$
--   The conclusion holds for every physical ancilla, including $p_A=0,1$ and $c_A=0$. Appendix C uses $4q$ as its coherence variable.
-- source:
--   Coherence -assisted quantum state preparation and thermal control through repeated interactions, arXiv:2610.10794v1, PDF p. 19, Appendix C Eqs.(C1)–(C4): nonnegativity of K

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P32

noncomputable section

open scoped Matrix ComplexConjugate Topology

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P32

/-- PDF p.19, Eqs.(C1)–(C4): nonnegativity for every physical ancilla. -/
theorem denominatorNonnegative (m : Model) : 0 ≤ denominatorK m := by sorry

end QAlgorithms.Papers.Independent.Information100.P32

end
