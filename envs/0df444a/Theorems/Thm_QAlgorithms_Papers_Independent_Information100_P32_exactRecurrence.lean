-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P32_exactRecurrence
-- name    : QAlgorithms.Papers.Independent.Information100.P32.exactRecurrence
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:25:31.005615+00:00
-- url     : https://prove2.me/theorems/573e8e66-7222-4609-a8f4-90a474ba5a5a
-- title:
--   Exact one-collision population and coherence recurrence
-- statement:
--   Let $J,\omega\in\mathbb R$ and $\tau>0$. Each fresh, independent ancillary qubit has the same state $\rho_A=\left(\begin{smallmatrix}p_A&c_A\\c_A^*&1-p_A\end{smallmatrix}\right)$, where $0\le p_A\le1$ and $|c_A|^2\le p_A(1-p_A)$. The system and incoming ancilla are initially uncorrelated. Put $H_S=H_A=-\omega\sigma_z/2$, $H_0=H_S\otimes I+I\otimes H_A$, and $H_I=J(\sigma_x\otimes\sigma_x+\sigma_y\otimes\sigma_y)$. One collision is $\Phi(\rho)=\operatorname{Tr}_A[e^{-i\tau(H_0+H_I)}(\rho\otimes\rho_A)e^{i\tau(H_0+H_I)}]$, with no additional free interval. Units are $\hbar=k_B=1$ and $|0\rangle$ has $\sigma_z$ eigenvalue $+1$. For every physical initial state and every $n\ge0$, let $p_n=(\Phi^n(\rho_0))_{00}$ and $c_n=(\Phi^n(\rho_0))_{01}$. Then
--   $$p_{n+1}=p_A+C^2(p_n-p_A)-\sin(4J\tau)\operatorname{Im}(c_nc_A^*),$$
--   $$c_{n+1}=e^{i\omega\tau}\bigl(Cc_n+i(2p_n-1)c_AS\bigr).$$
--   These exact identities include $J=0$ and $S=0$ and require no division by $K$.
-- source:
--   Coherence -assisted quantum state preparation and thermal control through repeated interactions, arXiv:2610.10794v1, PDF p. 3, §II B Eqs.(9)–(10): exact one-collision recurrence

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P32

noncomputable section

open scoped Matrix ComplexConjugate Topology

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P32

/-- PDF p.3, Eqs.(9)–(10): the recurrence is concluded from the constructed collision,
including zero coupling and S=0; no stationary denominator is used. -/
theorem exactRecurrence (m : Model) (r : Op Bool) (hr : IsDensityMatrix r) (n : ℕ) :
    let p := population (trajectory m r n)
    let c := coherence (trajectory m r n)
    population (trajectory m r (n + 1)) = m.pA + angleC m ^ 2 * (p - m.pA) -
      Real.sin (4 * m.coupling * m.duration) * (c * conj m.cA).im ∧
    coherence (trajectory m r (n + 1)) =
      Complex.exp (Complex.I * (m.frequency * m.duration : ℝ)) *
        ((c * (angleC m : ℂ)) + Complex.I * (2 * p - 1 : ℝ) * m.cA * (angleS m : ℂ)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P32

end
