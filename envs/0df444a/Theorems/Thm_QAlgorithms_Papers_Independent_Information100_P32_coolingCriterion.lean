-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P32_coolingCriterion
-- name    : QAlgorithms.Papers.Independent.Information100.P32.coolingCriterion
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:33:15.910157+00:00
-- url     : https://prove2.me/theorems/784e5ed6-1fdd-4fe1-bd92-692ed803d7fc
-- title:
--   Strict cooling criterion
-- statement:
--   Let $J,\omega\in\mathbb R$ and $\tau>0$. Each fresh, independent ancillary qubit has the same state $\rho_A=\left(\begin{smallmatrix}p_A&c_A\\c_A^*&1-p_A\end{smallmatrix}\right)$, where $0\le p_A\le1$ and $|c_A|^2\le p_A(1-p_A)$. The system and incoming ancilla are initially uncorrelated. Put $H_S=H_A=-\omega\sigma_z/2$, $H_0=H_S\otimes I+I\otimes H_A$, and $H_I=J(\sigma_x\otimes\sigma_x+\sigma_y\otimes\sigma_y)$. One collision is $\Phi(\rho)=\operatorname{Tr}_A[e^{-i\tau(H_0+H_I)}(\rho\otimes\rho_A)e^{i\tau(H_0+H_I)}]$, with no additional free interval. Units are $\hbar=k_B=1$ and $|0\rangle$ has $\sigma_z$ eigenvalue $+1$.
--
--   Write $C=\cos(2J\tau)$, $S=\sin(2J\tau)$, $L=C-\cos(\omega\tau)$, $q=|c_A|^2$, $x=2p_A-1$, $D=L^2+\sin^2(\omega\tau)$ and $K=D-4qCL$. The algebraic candidate $\rho_* =\rho(p_*,c_*)$ is constructed by
--   $$p_*=p_A+\frac{2qxCL}{K},\qquad c_*=-\frac{c_AxS}{K}\bigl(\sin(\omega\tau)+iL\bigr).$$
--
--   For statements about finite positive bath temperature, assume $1/2<p_A<1$ and $\omega>0$. Assume $c_A\ne0$, $K>0$ and $S\ne0$. Then
--   $$p_*>p_A\quad\Longleftrightarrow\quad C\bigl(C-\cos(\omega\tau)\bigr)>0.$$
--   Thus the sign of this collision-dependent factor determines strict population cooling. Also $p_*<p_A$ iff $CL<0$, and $p_*=p_A$ iff $CL=0$.
-- source:
--   Coherence -assisted quantum state preparation and thermal control through repeated interactions, arXiv:2610.10794v1, PDF p. 5, §III A Eq.(21): cooling criterion

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P32

noncomputable section

open scoped Matrix ComplexConjugate Topology

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P32

/-- PDF p.5, Eq.(21): cooling, heating and equal-population sign criteria for a
nonzero coherent positive-temperature ancilla. -/
theorem coolingCriterion (m : Model) (hp : 1 / 2 < m.pA) (hp1 : m.pA < 1)
    (hw : 0 < m.frequency) (hc : m.cA ≠ 0) (hK : 0 < denominatorK m)
    (hS : angleS m ≠ 0) :
    (m.pA < starPopulation m ↔ 0 < angleC m * differenceL m) ∧
    (starPopulation m < m.pA ↔ angleC m * differenceL m < 0) ∧
    (starPopulation m = m.pA ↔ angleC m * differenceL m = 0) := by sorry

end QAlgorithms.Papers.Independent.Information100.P32

end
