-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P32_coolingAndPurification
-- name    : QAlgorithms.Papers.Independent.Information100.P32.coolingAndPurification
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T10:38:57.792763+00:00
-- url     : https://prove2.me/theorems/2057fbf2-1161-494e-be42-f6e34ae33cb1
-- title:
--   Cooling implies purity gain; both converses fail
-- statement:
--   Let $J,\omega\in\mathbb R$ and $\tau>0$. Each fresh, independent ancillary qubit has the same state $\rho_A=\left(\begin{smallmatrix}p_A&c_A\\c_A^*&1-p_A\end{smallmatrix}\right)$, where $0\le p_A\le1$ and $|c_A|^2\le p_A(1-p_A)$. The system and incoming ancilla are initially uncorrelated. Put $H_S=H_A=-\omega\sigma_z/2$, $H_0=H_S\otimes I+I\otimes H_A$, and $H_I=J(\sigma_x\otimes\sigma_x+\sigma_y\otimes\sigma_y)$. One collision is $\Phi(\rho)=\operatorname{Tr}_A[e^{-i\tau(H_0+H_I)}(\rho\otimes\rho_A)e^{i\tau(H_0+H_I)}]$, with no additional free interval. Units are $\hbar=k_B=1$ and $|0\rangle$ has $\sigma_z$ eigenvalue $+1$.
--
--   Write $C=\cos(2J\tau)$, $S=\sin(2J\tau)$, $L=C-\cos(\omega\tau)$, $q=|c_A|^2$, $x=2p_A-1$, $D=L^2+\sin^2(\omega\tau)$ and $K=D-4qCL$. The algebraic candidate $\rho_* =\rho(p_*,c_*)$ is constructed by
--   $$p_*=p_A+\frac{2qxCL}{K},\qquad c_*=-\frac{c_AxS}{K}\bigl(\sin(\omega\tau)+iL\bigr).$$
--
--   For statements about finite positive bath temperature, assume $1/2<p_A<1$ and $\omega>0$. Assume $K>0$ and $S\ne0$, and put $\Delta p=p_*-p_A$. Then
--   $$\mathcal P(\rho_*)=p_A^2+(1-p_A)^2+2\Delta p^2+2\Delta p(2p_A-1)+2|c_*|^2.$$
--   Consequently $p_*>p_A$ implies $\mathcal P(\rho_*)>\mathcal P(\rho(p_A,0))$. There exist physical models in this same domain with $p_*=p_A$ and a strict purity gain, and others with $p_*<p_A$ and a strict purity gain. The reference is the diagonal thermal-ancilla state at the same $p_A$, not the coherent ancilla or initial system state.
-- source:
--   Coherence -assisted quantum state preparation and thermal control through repeated interactions, arXiv:2610.10794v1, PDF p. 5, §III B Eqs.(23)–(25): cooling implies purity gain, converse fails

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P32

noncomputable section

open scoped Matrix ComplexConjugate Topology

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P32

/-- PDF pp.5–7, Eqs.(23)–(25): cooling suffices for purity gain over the diagonal
ancilla reference; both noncooling and strictly heating examples give the converse failure. -/
theorem coolingAndPurification :
    (∀ m : Model, 1 / 2 < m.pA → m.pA < 1 → 0 < m.frequency →
      0 < denominatorK m → angleS m ≠ 0 →
      purity (starState m) = m.pA ^ 2 + (1 - m.pA) ^ 2 +
        2 * (starPopulation m - m.pA) ^ 2 +
        2 * (starPopulation m - m.pA) * (2 * m.pA - 1) + 2 * Complex.normSq (starCoherence m) ∧
      (m.pA < starPopulation m → purity (rho m.pA 0) < purity (starState m))) ∧
    (∃ m : Model, 1 / 2 < m.pA ∧ m.pA < 1 ∧ 0 < m.frequency ∧
      0 < denominatorK m ∧ angleS m ≠ 0 ∧ starPopulation m = m.pA ∧
      purity (rho m.pA 0) < purity (starState m)) ∧
    (∃ m : Model, 1 / 2 < m.pA ∧ m.pA < 1 ∧ 0 < m.frequency ∧
      0 < denominatorK m ∧ angleS m ≠ 0 ∧ starPopulation m < m.pA ∧
      purity (rho m.pA 0) < purity (starState m)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P32

end
