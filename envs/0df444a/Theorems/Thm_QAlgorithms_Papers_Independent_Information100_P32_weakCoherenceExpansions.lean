-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P32_weakCoherenceExpansions
-- name    : QAlgorithms.Papers.Independent.Information100.P32.weakCoherenceExpansions
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T10:32:21.083813+00:00
-- url     : https://prove2.me/theorems/3695b31e-ce59-478c-bf3b-28a57d13ba23
-- title:
--   Weak-coherence expansion with exact remainder orders
-- statement:
--   Let $J,\omega\in\mathbb R$ and $\tau>0$. Each fresh, independent ancillary qubit has the same state $\rho_A=\left(\begin{smallmatrix}p_A&c_A\\c_A^*&1-p_A\end{smallmatrix}\right)$, where $0\le p_A\le1$ and $|c_A|^2\le p_A(1-p_A)$. The system and incoming ancilla are initially uncorrelated. Put $H_S=H_A=-\omega\sigma_z/2$, $H_0=H_S\otimes I+I\otimes H_A$, and $H_I=J(\sigma_x\otimes\sigma_x+\sigma_y\otimes\sigma_y)$. One collision is $\Phi(\rho)=\operatorname{Tr}_A[e^{-i\tau(H_0+H_I)}(\rho\otimes\rho_A)e^{i\tau(H_0+H_I)}]$, with no additional free interval. Units are $\hbar=k_B=1$ and $|0\rangle$ has $\sigma_z$ eigenvalue $+1$.
--
--   Write $C=\cos(2J\tau)$, $S=\sin(2J\tau)$, $L=C-\cos(\omega\tau)$, $q=|c_A|^2$, $x=2p_A-1$, $D=L^2+\sin^2(\omega\tau)$ and $K=D-4qCL$. The algebraic candidate $\rho_* =\rho(p_*,c_*)$ is constructed by
--   $$p_*=p_A+\frac{2qxCL}{K},\qquad c_*=-\frac{c_AxS}{K}\bigl(\sin(\omega\tau)+iL\bigr).$$ Fix $0<p_A<1$ and parameters with $D>0$, and vary the complex ancillary coherence $c$ near zero. There is a neighborhood in which the ancillary state is physical and $K(c)>0$. With $u=(\sin(\omega\tau)+iL)/\sqrt D$,
--   $$p_*(c)=p_A+\frac{2|c|^2xCL}{D}+O(|c|^4),\qquad c_*(c)=-\frac{cxS}{\sqrt D}u+O(|c|^3).$$
--   Both remainder estimates hold as $c\to0$; coefficients may vanish at special collision parameters.
-- source:
--   Coherence -assisted quantum state preparation and thermal control through repeated interactions, arXiv:2610.10794v1, PDF p. 4, §II B Eqs.(16),(20): weak-coherence expansions

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P32

noncomputable section

open scoped Matrix ComplexConjugate Topology

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P32

/-- PDF p.4, Eqs.(16),(20): quadratic population and linear coherence terms, with
fourth- and third-order remainders. The neighborhood remains physical and K-positive. -/
theorem weakCoherenceExpansions (m : Model) (hp : 0 < m.pA) (hp1 : m.pA < 1)
    (hD : 0 < denominatorD m) :
    (∃ delta : ℝ, 0 < delta ∧ ∀ c : ℂ, ‖c‖ < delta →
      Physical m.pA c ∧ 0 < denominatorD m - 4 * Complex.normSq c * angleC m * differenceL m) ∧
    Asymptotics.IsBigO (𝓝 (0 : ℂ))
      (fun c => varyingPopulation m c - (m.pA +
        2 * Complex.normSq c * (2 * m.pA - 1) * angleC m * differenceL m / denominatorD m))
      (fun c : ℂ => ‖c‖ ^ 4) ∧
    Asymptotics.IsBigO (𝓝 (0 : ℂ))
      (fun c => varyingCoherence m c -
        (-c * (2 * m.pA - 1 : ℝ) * (angleS m : ℂ) /
          (Real.sqrt (denominatorD m) : ℂ) * phase m))
      (fun c : ℂ => ‖c‖ ^ 3) := by sorry

end QAlgorithms.Papers.Independent.Information100.P32

end
