-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P97_zero_error_attainability
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P97.zero_error_attainability
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:53:49.770148+00:00
-- url     : https://prove2.me/theorems/db0a6aee-b3f7-4f0a-b41b-a57ed4956939
-- title:
--   Prescribed ancillary overlap and exact cloning by identity evolution
-- statement:
--   All states are positive semidefinite, trace-one matrices, including pure and rank-deficient states. Write $F(\rho,\sigma)$ for squared Uhlmann fidelity, $f=\sqrt{F(\rho_1,\rho_2)}$, and $D(\rho,\sigma)=\sqrt{1-F(\rho,\sigma)}=\sin\Delta(\rho,\sigma)$.
--
--   Let $d>1$ and let $\rho_1\ne\rho_2$ be density operators on $H=\mathbb C^d$. For every prescribed real $0\le\phi\le f$, there exist unit vectors $Y_1,Y_2\in H_B\otimes H_E$, with $H_B=H_E=H$, whose pure density operators $\Upsilon_j=|Y_j\rangle\langle Y_j|$ satisfy
--
--   $$\operatorname{Tr}_E\Upsilon_j=\rho_j\quad(j=1,2),\qquad\sqrt{F(\Upsilon_1,\Upsilon_2)}=\phi,\qquad R_{V=I}=0.$$
--
--   Here $R$ is the joint-output relative error from Eq. (14), starting from $\rho_j\otimes\Upsilon_j$. This establishes sharpness of the zero lower bound through a constructed ancillary pair.
-- source:
--   Lower bound on the relative error of mixed-state cloning and related operations, arXiv:quant-ph/0208159v2, PDF p. 4, §IV, proof of Theorem (ii), Eqs. (20)–(21)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P97

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Intakenext100.P97

open QAlgorithms.Papers.Independent.Information100.P67
  (squaredFidelity sineDistance receiverChannel)

open QAlgorithms.Papers.Independent.Dependency50.P48 (densityPower)

/-- PDF p.4, proof of Theorem (ii), Eqs. (20)--(21).
For each prescribed ancillary root fidelity in `[0,f]`, normalized pure
ancillas on `H tensor H` are constructed existentially; identity evolution
then attains zero error. No arbitrary fixed ancillary pair is asserted to work. -/
theorem zero_error_attainability {d : ℕ} (hd : 1 < d)
    (rho1 rho2 : Matrix (Fin d) (Fin d) ℂ)
    (hrho1 : IsDensityMatrix rho1) (hrho2 : IsDensityMatrix rho2)
    (hdistinct : rho1 ≠ rho2) (phi : ℝ)
    (hphi0 : 0 ≤ phi) (hphif : phi ≤ rootFidelity rho1 rho2) :
    ∃ Y1 Y2 : EuclideanSpace ℂ (Fin d × Fin d),
      IsState Y1 ∧ IsState Y2 ∧
      traceRight (pureDensity Y1) = rho1 ∧ traceRight (pureDensity Y2) = rho2 ∧
      rootFidelity (pureDensity Y1) (pureDensity Y2) = phi ∧
      oneToTwoError rho1 rho2 (pureDensity Y1) (pureDensity Y2) 1 = 0 := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P97

end
