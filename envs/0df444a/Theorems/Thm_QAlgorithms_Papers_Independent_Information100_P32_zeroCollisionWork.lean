-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P32_zeroCollisionWork
-- name    : QAlgorithms.Papers.Independent.Information100.P32.zeroCollisionWork
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T10:40:58.579455+00:00
-- url     : https://prove2.me/theorems/5b77b3ca-1f60-4c53-877b-85916efcb523
-- title:
--   Every collision has zero switching work
-- statement:
--   Let $J,\omega\in\mathbb R$ and $\tau>0$. Each fresh, independent ancillary qubit has the same state $\rho_A=\left(\begin{smallmatrix}p_A&c_A\\c_A^*&1-p_A\end{smallmatrix}\right)$, where $0\le p_A\le1$ and $|c_A|^2\le p_A(1-p_A)$. The system and incoming ancilla are initially uncorrelated. Put $H_S=H_A=-\omega\sigma_z/2$, $H_0=H_S\otimes I+I\otimes H_A$, and $H_I=J(\sigma_x\otimes\sigma_x+\sigma_y\otimes\sigma_y)$. One collision is $\Phi(\rho)=\operatorname{Tr}_A[e^{-i\tau(H_0+H_I)}(\rho\otimes\rho_A)e^{i\tau(H_0+H_I)}]$, with no additional free interval. Units are $\hbar=k_B=1$ and $|0\rangle$ has $\sigma_z$ eigenvalue $+1$. For every physical system input $\rho$, put $U=e^{-i\tau(H_0+H_I)}$ and define the source's work sign by
--   $$W=\operatorname{Tr}[(U^\dagger H_IU-H_I)(\rho\otimes\rho_A)].$$
--   Then $[H_I,U]=0$ and $W=0$. These are conclusions from the constructed resonant Hamiltonian.
-- source:
--   Coherence -assisted quantum state preparation and thermal control through repeated interactions, arXiv:2610.10794v1, PDF p. 9, §IV Eq.(34): zero collision work

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P32

noncomputable section

open scoped Matrix ComplexConjugate Topology

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P32

/-- PDF p.9, Eq.(34): commutation and zero collision work are conclusions. -/
theorem zeroCollisionWork (m : Model) (r : Op Bool) (hr : IsDensityMatrix r) :
    Commute (interaction m.coupling)
      (evolution (freeEnergy m.frequency + interaction m.coupling) m.duration) ∧ work m r = 0 := by sorry

end QAlgorithms.Papers.Independent.Information100.P32

end
