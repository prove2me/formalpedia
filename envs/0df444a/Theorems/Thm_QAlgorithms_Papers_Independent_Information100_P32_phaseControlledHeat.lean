-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P32_phaseControlledHeat
-- name    : QAlgorithms.Papers.Independent.Information100.P32.phaseControlledHeat
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T10:42:10.962278+00:00
-- url     : https://prove2.me/theorems/53d45a18-1855-4691-bfe6-19783ad9413f
-- title:
--   Coherent heat depends on relative phase and can reverse total heat
-- statement:
--   Let $J,\omega\in\mathbb R$ and $\tau>0$. Each fresh, independent ancillary qubit has the same state $\rho_A=\left(\begin{smallmatrix}p_A&c_A\\c_A^*&1-p_A\end{smallmatrix}\right)$, where $0\le p_A\le1$ and $|c_A|^2\le p_A(1-p_A)$. The system and incoming ancilla are initially uncorrelated. Put $H_S=H_A=-\omega\sigma_z/2$, $H_0=H_S\otimes I+I\otimes H_A$, and $H_I=J(\sigma_x\otimes\sigma_x+\sigma_y\otimes\sigma_y)$. One collision is $\Phi(\rho)=\operatorname{Tr}_A[e^{-i\tau(H_0+H_I)}(\rho\otimes\rho_A)e^{i\tau(H_0+H_I)}]$, with no additional free interval. Units are $\hbar=k_B=1$ and $|0\rangle$ has $\sigma_z$ eigenvalue $+1$. For a physical system input write $c=|c|e^{i\phi_S}$ and $c_A=|c_A|e^{i\phi_A}$. With $Q_{\rm coh}$ defined by the off-diagonal ancillary operator as above,
--   $$Q_{\rm coh}=-\omega|c||c_A|\sin(4J\tau)\sin(\phi_S-\phi_A).$$
--   There exist physical inputs with $\omega>0$, $1/2<p,p_A<1$ and $(p_A-p)Q<0$, where $Q$ is total heat into the ancilla. This witnesses anomalous heat against the population imbalance. Vanishing coherences or $\sin(4J\tau)=0$ give zero coherent heat for every phase; the relative phase alone does not determine total heat. There also exist physical coherent inputs with $1/2<p_S=p_A<1$, $\omega>0$, and nonzero total heat in one collision.
-- source:
--   Coherence -assisted quantum state preparation and thermal control through repeated interactions, arXiv:2610.10794v1, PDF p. 10, §IV Eq.(40): relative phase controls coherent heat, including anomalous transfer

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P32

noncomputable section

open scoped Matrix ComplexConjugate Topology

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P32

/-- PDF pp.10–12, Eq.(40): relative phase controls the coherent term; anomalous
heat at equal populations and total heat against a nonzero population imbalance
are possible for physical inputs. -/
theorem phaseControlledHeat :
    (∀ (m : Model) (r : Op Bool), IsDensityMatrix r → ∀ phiS phiA : ℝ,
      coherence r = (‖coherence r‖ : ℂ) * Complex.exp (Complex.I * phiS) →
      m.cA = (‖m.cA‖ : ℂ) * Complex.exp (Complex.I * phiA) →
      heat m r (offDiagonalAncilla m) = -m.frequency * ‖coherence r‖ * ‖m.cA‖ *
        Real.sin (4 * m.coupling * m.duration) * Real.sin (phiS - phiA)) ∧
    (∃ (m : Model) (r : Op Bool), IsDensityMatrix r ∧ 0 < m.frequency ∧
      1 / 2 < m.pA ∧ m.pA < 1 ∧ population r = m.pA ∧
      heat m r (rho m.pA m.cA) ≠ 0) ∧
    (∃ (m : Model) (r : Op Bool), IsDensityMatrix r ∧ 0 < m.frequency ∧
      1 / 2 < m.pA ∧ m.pA < 1 ∧ 1 / 2 < population r ∧ population r < 1 ∧
      (m.pA - population r) * heat m r (rho m.pA m.cA) < 0) := by sorry

end QAlgorithms.Papers.Independent.Information100.P32

end
