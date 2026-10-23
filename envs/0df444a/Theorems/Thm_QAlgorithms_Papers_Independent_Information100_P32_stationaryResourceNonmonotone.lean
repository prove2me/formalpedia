-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P32_stationaryResourceNonmonotone
-- name    : QAlgorithms.Papers.Independent.Information100.P32.stationaryResourceNonmonotone
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T10:54:27.925864+00:00
-- url     : https://prove2.me/theorems/0dbb8bcd-6dc7-429c-a9a1-b5b6786f59c2
-- title:
--   Stationary resource coherence can have an interior peak
-- statement:
--   Let $J,\omega\in\mathbb R$ and $\tau>0$. Each fresh, independent ancillary qubit has the same state $\rho_A=\left(\begin{smallmatrix}p_A&c_A\\c_A^*&1-p_A\end{smallmatrix}\right)$, where $0\le p_A\le1$ and $|c_A|^2\le p_A(1-p_A)$. The system and incoming ancilla are initially uncorrelated. Put $H_S=H_A=-\omega\sigma_z/2$, $H_0=H_S\otimes I+I\otimes H_A$, and $H_I=J(\sigma_x\otimes\sigma_x+\sigma_y\otimes\sigma_y)$. One collision is $\Phi(\rho)=\operatorname{Tr}_A[e^{-i\tau(H_0+H_I)}(\rho\otimes\rho_A)e^{i\tau(H_0+H_I)}]$, with no additional free interval. Units are $\hbar=k_B=1$ and $|0\rangle$ has $\sigma_z$ eigenvalue $+1$.
--
--   Write $C=\cos(2J\tau)$, $S=\sin(2J\tau)$, $L=C-\cos(\omega\tau)$, $q=|c_A|^2$, $x=2p_A-1$, $D=L^2+\sin^2(\omega\tau)$ and $K=D-4qCL$. The algebraic candidate $\rho_* =\rho(p_*,c_*)$ is constructed by
--   $$p_*=p_A+\frac{2qxCL}{K},\qquad c_*=-\frac{c_AxS}{K}\bigl(\sin(\omega\tau)+iL\bigr).$$ There exist fixed $J,\omega,\tau,p_A$ with $\omega>0$, $1/2<p_A<1$ and $S\ne0$, and three real nonnegative ancillary coherences $0\le a<b<c$, all physical with $K>0$, for which both stationary coherence measures have an interior peak:
--   $$C_{l_1}(\rho_*(a))<C_{l_1}(\rho_*(b))>C_{l_1}(\rho_*(c)),\qquad
--   C_{\rm rel}(\rho_*(a))<C_{\rm rel}(\rho_*(b))>C_{\rm rel}(\rho_*(c)).$$
--   Here $C_{l_1}(\rho)=\sum_{i\ne j}|\rho_{ij}|$ and $C_{\rm rel}(\rho)=S(\mathcal D\rho)-S(\rho)$ with entropy in nats. This is the paper's existence observation, not a universal monotonicity claim.
-- source:
--   Coherence -assisted quantum state preparation and thermal control through repeated interactions, arXiv:2610.10794v1, PDF p. 23, Appendix F Figs.10–11: stationary resource coherence can be nonmonotone

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P32

noncomputable section

open scoped Matrix ComplexConjugate Topology

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P32

/-- PDF pp.21–24, Appendix F, Figs.10–11: both resource measures can have an
interior peak as environmental coherence increases with other parameters fixed. -/
theorem stationaryResourceNonmonotone :
    ∃ a b c : Model,
      a.coupling = b.coupling ∧ b.coupling = c.coupling ∧
      a.frequency = b.frequency ∧ b.frequency = c.frequency ∧
      a.duration = b.duration ∧ b.duration = c.duration ∧ a.pA = b.pA ∧ b.pA = c.pA ∧
      1 / 2 < a.pA ∧ a.pA < 1 ∧ 0 < a.frequency ∧ angleS a ≠ 0 ∧
      0 < denominatorK a ∧ 0 < denominatorK b ∧ 0 < denominatorK c ∧
      a.cA.im = 0 ∧ b.cA.im = 0 ∧ c.cA.im = 0 ∧ 0 ≤ a.cA.re ∧
      a.cA.re < b.cA.re ∧ b.cA.re < c.cA.re ∧
      resourceL1 (starState a) < resourceL1 (starState b) ∧
      resourceL1 (starState c) < resourceL1 (starState b) ∧
      resourceEntropy (starState a) < resourceEntropy (starState b) ∧
      resourceEntropy (starState c) < resourceEntropy (starState b) := by sorry

end QAlgorithms.Papers.Independent.Information100.P32

end
