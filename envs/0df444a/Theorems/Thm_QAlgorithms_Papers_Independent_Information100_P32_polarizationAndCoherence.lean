-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P32_polarizationAndCoherence
-- name    : QAlgorithms.Papers.Independent.Information100.P32.polarizationAndCoherence
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:27:16.906462+00:00
-- url     : https://prove2.me/theorems/13441112-19e9-45ab-9b64-c5e0b3a4c378
-- title:
--   Polarization and coherence factorization
-- statement:
--   Let $J,\omega\in\mathbb R$ and $\tau>0$. Each fresh, independent ancillary qubit has the same state $\rho_A=\left(\begin{smallmatrix}p_A&c_A\\c_A^*&1-p_A\end{smallmatrix}\right)$, where $0\le p_A\le1$ and $|c_A|^2\le p_A(1-p_A)$. The system and incoming ancilla are initially uncorrelated. Put $H_S=H_A=-\omega\sigma_z/2$, $H_0=H_S\otimes I+I\otimes H_A$, and $H_I=J(\sigma_x\otimes\sigma_x+\sigma_y\otimes\sigma_y)$. One collision is $\Phi(\rho)=\operatorname{Tr}_A[e^{-i\tau(H_0+H_I)}(\rho\otimes\rho_A)e^{i\tau(H_0+H_I)}]$, with no additional free interval. Units are $\hbar=k_B=1$ and $|0\rangle$ has $\sigma_z$ eigenvalue $+1$.
--
--   Write $C=\cos(2J\tau)$, $S=\sin(2J\tau)$, $L=C-\cos(\omega\tau)$, $q=|c_A|^2$, $x=2p_A-1$, $D=L^2+\sin^2(\omega\tau)$ and $K=D-4qCL$. The algebraic candidate $\rho_* =\rho(p_*,c_*)$ is constructed by
--   $$p_*=p_A+\frac{2qxCL}{K},\qquad c_*=-\frac{c_AxS}{K}\bigl(\sin(\omega\tau)+iL\bigr).$$ For $K>0$, put $\Lambda=4qCL/D$ and $u=(\sin(\omega\tau)+iL)/\sqrt D$. Then $D>0$, $|u|=1$, and
--   $$K=D(1-\Lambda),\qquad 2p_*-1=\frac{x}{1-\Lambda},$$
--   $$c_*=-\frac{c_AxS}{\sqrt D(1-\Lambda)}u=-\frac{c_A(2p_*-1)S}{\sqrt D}u.$$
--   If $p_A\ne1/2$, also $(2p_*-1)/(2p_A-1)=1/(1-\Lambda)$. The undivided identity remains valid at $p_A=1/2$.
-- source:
--   Coherence -assisted quantum state preparation and thermal control through repeated interactions, arXiv:2610.10794v1, PDF p. 4, §II B Eqs.(14)–(19): polarization and coherence formulas

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P32

noncomputable section

open scoped Matrix ComplexConjugate Topology

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P32

/-- PDF p.4, Eqs.(14)–(19): sqrt(D) multiplies (1-Lambda), and the phase is constructed. -/
theorem polarizationAndCoherence (m : Model) (hK : 0 < denominatorK m) :
    0 < denominatorD m ∧ denominatorK m = denominatorD m * (1 - lambda m) ∧
    (2 * starPopulation m - 1) = (2 * m.pA - 1) / (1 - lambda m) ∧
    (m.pA ≠ 1 / 2 → (2 * starPopulation m - 1) / (2 * m.pA - 1) = 1 / (1 - lambda m)) ∧
    ‖phase m‖ = 1 ∧
    starCoherence m = -m.cA * (2 * m.pA - 1 : ℝ) * (angleS m : ℂ) /
      ((Real.sqrt (denominatorD m) * (1 - lambda m) : ℝ) : ℂ) * phase m ∧
    starCoherence m = -m.cA * (2 * starPopulation m - 1 : ℝ) * (angleS m : ℂ) /
      (Real.sqrt (denominatorD m) : ℂ) * phase m := by sorry

end QAlgorithms.Papers.Independent.Information100.P32

end
