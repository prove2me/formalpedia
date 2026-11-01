-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P97_measurement_outcome_stability
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P97.measurement_outcome_stability
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:53:08.084047+00:00
-- url     : https://prove2.me/theorems/5f97b3fd-778a-43b2-a72e-795f7df35017
-- title:
--   Every measurement outcome is stable in sine distance
-- statement:
--   All states are positive semidefinite, trace-one matrices, including pure and rank-deficient states. Write $F(\rho,\sigma)$ for squared Uhlmann fidelity, $f=\sqrt{F(\rho_1,\rho_2)}$, and $D(\rho,\sigma)=\sqrt{1-F(\rho,\sigma)}=\sin\Delta(\rho,\sigma)$.
--
--   Let $\chi$ and $\omega$ be density operators on the same finite-dimensional system. For any measurement outcome with effect $0\preceq E_a\preceq I$, put $p(a\mid\rho)=\operatorname{Tr}(E_a\rho)$. Then
--
--   $$|p(a\mid\chi)-p(a\mid\omega)|\le D(\chi,\omega).$$
--
--   This single-outcome estimate holds for arbitrary measurements: every outcome is an effect, and every effect is an outcome of the two-outcome POVM $\{E_a,I-E_a\}$.
-- source:
--   Lower bound on the relative error of mixed-state cloning and related operations, arXiv:quant-ph/0208159v2, PDF p. 2, §II, Lemma 2, Eq. (7)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P97

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Intakenext100.P97

open QAlgorithms.Papers.Independent.Information100.P67
  (squaredFidelity sineDistance receiverChannel)

open QAlgorithms.Papers.Independent.Dependency50.P48 (densityPower)

/-- PDF p.2, §II, Lemma 2, Eq. (7). An arbitrary outcome effect covers
all measurements, without restricting their number of outcomes. -/
theorem measurement_outcome_stability {d : ℕ}
    (chi omega effect : Matrix (Fin d) (Fin d) ℂ)
    (hchi : IsDensityMatrix chi) (homega : IsDensityMatrix omega)
    (heffect : IsEffect effect) :
    |effectProb effect chi - effectProb effect omega| ≤ sineDistance chi omega := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P97

end
