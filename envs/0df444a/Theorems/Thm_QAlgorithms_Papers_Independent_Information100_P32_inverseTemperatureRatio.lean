-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P32_inverseTemperatureRatio
-- name    : QAlgorithms.Papers.Independent.Information100.P32.inverseTemperatureRatio
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T10:40:11.074991+00:00
-- url     : https://prove2.me/theorems/72f112b0-126e-440f-af40-2a70c6f81c18
-- title:
--   Population-defined inverse-temperature ratio
-- statement:
--   Let $J,\omega\in\mathbb R$ and $\tau>0$. Each fresh, independent ancillary qubit has the same state $\rho_A=\left(\begin{smallmatrix}p_A&c_A\\c_A^*&1-p_A\end{smallmatrix}\right)$, where $0\le p_A\le1$ and $|c_A|^2\le p_A(1-p_A)$. The system and incoming ancilla are initially uncorrelated. Put $H_S=H_A=-\omega\sigma_z/2$, $H_0=H_S\otimes I+I\otimes H_A$, and $H_I=J(\sigma_x\otimes\sigma_x+\sigma_y\otimes\sigma_y)$. One collision is $\Phi(\rho)=\operatorname{Tr}_A[e^{-i\tau(H_0+H_I)}(\rho\otimes\rho_A)e^{i\tau(H_0+H_I)}]$, with no additional free interval. Units are $\hbar=k_B=1$ and $|0\rangle$ has $\sigma_z$ eigenvalue $+1$.
--
--   Write $C=\cos(2J\tau)$, $S=\sin(2J\tau)$, $L=C-\cos(\omega\tau)$, $q=|c_A|^2$, $x=2p_A-1$, $D=L^2+\sin^2(\omega\tau)$ and $K=D-4qCL$. The algebraic candidate $\rho_* =\rho(p_*,c_*)$ is constructed by
--   $$p_*=p_A+\frac{2qxCL}{K},\qquad c_*=-\frac{c_AxS}{K}\bigl(\sin(\omega\tau)+iL\bigr).$$
--
--   For statements about finite positive bath temperature, assume $1/2<p_A<1$ and $\omega>0$. Assume $K>0$ and $0<p_*<1$. Define $\beta(p)=\omega^{-1}\log[p/(1-p)]$. Then
--   $$\beta(p_*)=\frac1\omega\log\frac{2p_A-\Lambda}{2(1-p_A)-\Lambda},\qquad
--   \frac{\beta(p_*)}{\beta(p_A)}=\frac{\operatorname{artanh}(x/(1-\Lambda))}{\operatorname{artanh}(x)}.$$
--   Here $\Lambda=4qCL/D$. These are population-defined temperatures for coherent states; the dephased limits are Gibbs states. Moreover, $\beta(p_*)/\beta(p_A)>1$ iff $p_*>p_A$, and the ratio is below one iff $p_*<p_A$.
-- source:
--   Coherence -assisted quantum state preparation and thermal control through repeated interactions, arXiv:2610.10794v1, PDF p. 8, §III C Eqs.(31)–(33): inverse-temperature ratio

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P32

noncomputable section

open scoped Matrix ComplexConjugate Topology

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P32

/-- PDF pp.8–9, Eqs.(31)–(33): finite population-defined inverse temperature.
The coherent stationary state becomes a Gibbs state only after dephasing;
the inverse-temperature ratio classifies cooling and heating. -/
theorem inverseTemperatureRatio (m : Model) (hp : 1 / 2 < m.pA) (hp1 : m.pA < 1)
    (hw : 0 < m.frequency) (hK : 0 < denominatorK m)
    (hs0 : 0 < starPopulation m) (hs1 : starPopulation m < 1) :
    inverseTemperature m.frequency (starPopulation m) =
      Real.log ((2 * m.pA - lambda m) / (2 * (1 - m.pA) - lambda m)) / m.frequency ∧
    inverseTemperature m.frequency (starPopulation m) / inverseTemperature m.frequency m.pA =
      Real.artanh ((2 * m.pA - 1) / (1 - lambda m)) / Real.artanh (2 * m.pA - 1) ∧
    (1 < inverseTemperature m.frequency (starPopulation m) / inverseTemperature m.frequency m.pA ↔
      m.pA < starPopulation m) ∧
    (inverseTemperature m.frequency (starPopulation m) / inverseTemperature m.frequency m.pA < 1 ↔
      starPopulation m < m.pA) := by sorry

end QAlgorithms.Papers.Independent.Information100.P32

end
