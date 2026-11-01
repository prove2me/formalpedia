-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P97_fidelity_variation
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P97.fidelity_variation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:52:29.119733+00:00
-- url     : https://prove2.me/theorems/8f8cc4bd-3fa5-43bc-b318-8a13841ef9cb
-- title:
--   Squared-fidelity variation is bounded by sine distance
-- statement:
--   All states are positive semidefinite, trace-one matrices, including pure and rank-deficient states. Write $F(\rho,\sigma)$ for squared Uhlmann fidelity, $f=\sqrt{F(\rho_1,\rho_2)}$, and $D(\rho,\sigma)=\sqrt{1-F(\rho,\sigma)}=\sin\Delta(\rho,\sigma)$.
--
--   For any three density operators $\chi,\omega,\rho$ on the same finite-dimensional system,
--
--   $$|F(\chi,\rho)-F(\omega,\rho)|\le D(\chi,\omega).$$
--
--   This controls changes in fidelity with a fixed reference state, including equality and orthogonality of $\chi$ and $\omega$.
-- source:
--   Lower bound on the relative error of mixed-state cloning and related operations, arXiv:quant-ph/0208159v2, PDF p. 2, §II, Lemma 1, Eq. (5)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P97

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Intakenext100.P97

open QAlgorithms.Papers.Independent.Information100.P67
  (squaredFidelity sineDistance receiverChannel)

open QAlgorithms.Papers.Independent.Dependency50.P48 (densityPower)

/-- PDF p.2, §II, Lemma 1, Eq. (5). Absolute-value bars are visible
in the PDF; `F` is squared fidelity, not the root fidelity. -/
theorem fidelity_variation {d : ℕ} (chi omega rho : Matrix (Fin d) (Fin d) ℂ)
    (hchi : IsDensityMatrix chi) (homega : IsDensityMatrix omega)
    (hrho : IsDensityMatrix rho) :
    |squaredFidelity chi rho - squaredFidelity omega rho| ≤ sineDistance chi omega := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P97

end
