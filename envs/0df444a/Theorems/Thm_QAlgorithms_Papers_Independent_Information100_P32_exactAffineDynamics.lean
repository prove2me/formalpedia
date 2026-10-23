-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P32_exactAffineDynamics
-- name    : QAlgorithms.Papers.Independent.Information100.P32.exactAffineDynamics
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T10:46:27.531603+00:00
-- url     : https://prove2.me/theorems/403e2bcb-9438-40f9-abc0-79aaa6a778f4
-- title:
--   Exact affine vector form of the collision trajectory
-- statement:
--   Let $J,\omega\in\mathbb R$ and $\tau>0$. Each fresh, independent ancillary qubit has the same state $\rho_A=\left(\begin{smallmatrix}p_A&c_A\\c_A^*&1-p_A\end{smallmatrix}\right)$, where $0\le p_A\le1$ and $|c_A|^2\le p_A(1-p_A)$. The system and incoming ancilla are initially uncorrelated. Put $H_S=H_A=-\omega\sigma_z/2$, $H_0=H_S\otimes I+I\otimes H_A$, and $H_I=J(\sigma_x\otimes\sigma_x+\sigma_y\otimes\sigma_y)$. One collision is $\Phi(\rho)=\operatorname{Tr}_A[e^{-i\tau(H_0+H_I)}(\rho\otimes\rho_A)e^{i\tau(H_0+H_I)}]$, with no additional free interval. Units are $\hbar=k_B=1$ and $|0\rangle$ has $\sigma_z$ eigenvalue $+1$. For every initial density matrix and every $n\ge0$, put $X_n=(p_n,c_n,c_n^*)^T$, $e=e^{i\omega\tau}$, $C=\cos(2J\tau)$ and $S=\sin(2J\tau)$. Then
--   $$X_{n+1}=MX_n+\Upsilon,$$
--   $$M=\begin{pmatrix}C^2&\frac i2\sin(4J\tau)c_A^*&-\frac i2\sin(4J\tau)c_A\\2ic_AS e&Ce&0\\-2ic_A^*S e^*&0&Ce^*\end{pmatrix},\quad
--   \Upsilon=\begin{pmatrix}p_AS^2\\-ic_AS e\\ic_A^*S e^*\end{pmatrix}.$$
--   This is the exact discrete dynamics, without a continuous-time approximation.
-- source:
--   Coherence -assisted quantum state preparation and thermal control through repeated interactions, arXiv:2610.10794v1, PDF p. 18, Appendix B Eqs.(B1)–(B3): exact affine discrete dynamics

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P32

noncomputable section

open scoped Matrix ComplexConjugate Topology

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P32

/-- PDF p.18, Eqs.(B1)–(B3): exact affine dynamics, with no continuous limit. -/
theorem exactAffineDynamics (m : Model) (r : Op Bool) (hr : IsDensityMatrix r) (n : ℕ) :
    coordinates (trajectory m r (n + 1)) =
      (affineMatrix m).mulVec (coordinates (trajectory m r n)) + affineOffset m := by sorry

end QAlgorithms.Papers.Independent.Information100.P32

end
