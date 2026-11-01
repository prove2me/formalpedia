-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P53_qutrit_two_port_spin_block
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P53.qutrit_two_port_spin_block
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:33:49.002586+00:00
-- url     : https://prove2.me/theorems/1c667c22-122c-4651-ac9c-32a2e4ca749f
-- title:
--   The physical qutrit two-port spin block and complete kernel
-- statement:
--   Take $d=3,N=2$, with the physical signal sum $\rho=\frac13(P^-_{A_1C}\otimes I_{A_2}+P^-_{A_2C}\otimes I_{A_1})$. Construct the nine orthonormal coupled states $|1,m;J\rangle$ of $CA_1A_2$, where $m=-1,0,1$ and the physical $A$-spin is $J=0,1,2$, using real highest-weight coefficients and physical lowering. Choose phases so the $A_1C$ singlet matrix has sign $(-1)^{J+J'}$. Then
--   $$\langle1,m;J|P^-_{A_iC}|1,m;J'\rangle=\frac{\sqrt{(2J+1)(2J'+1)}}9\begin{cases}(-1)^{J+J'},&i=1,\\1,&i=2.\end{cases}$$
--   The operator vanishes outside total spin one, and every magnetic block is
--   $$\rho(1,m)=\frac2{27}\begin{pmatrix}1&0&\sqrt5\\0&3&0\\\sqrt5&0&5\end{pmatrix}.$$
--   In particular it does not commute with $S_A^2$. Its eigenvalues are $4/9$ and $2/9$, each of multiplicity three, together with a 21-dimensional kernel. In each magnetic block the normalized null vector is $\kappa_m=(\sqrt5|1,m;0\rangle-|1,m;2\rangle)/\sqrt6$, and the complete kernel projector is
--   $$I-\operatorname{supp}\rho=I-P_{\mathrm{total}=1}+\sum_m|\kappa_m\rangle\langle\kappa_m|.$$
--
--   This preserves the physical spin interpretation of the block. Printed Eq.(B7)'s coefficient $5$ and incomplete kernel complement are corrected by the uniquely determining Eq.(B2).
-- source:
--   Some remarks on port-based teleportation, arXiv:1506.01555v2, PDF p. 6, Appendix B Eqs.(B1)-(B2): qutrit two-port physical spin block

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P53

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P53

open scoped Classical ComplexConjugate ComplexOrder Matrix Matrix.Norms.L2Operator

-- Accepted generic matrix and positive-operator interfaces. The support is the
-- orthogonal range projection; all uses below are on positive physical rho.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Next46.P39 (inverseSqrt)

/-- PDF pp.6-7, Eqs.(B1)-(B2),(B7): the actual qutrit two-port block and
spectrum. Printed B7's null coefficient 5 becomes sqrt(5); the complete kernel
also includes every total-spin sector outside spin one, not just spin three. -/
theorem qutrit_two_port_spin_block :
    qutritFullFrameᴴ * qutritFullFrame = 1 ∧
    (∀ r J : Fin 3,
      QAlgorithms.act (totalCasimir 3 2) (qutritCoupled r J) = (2 : ℂ) • qutritCoupled r J ∧
      QAlgorithms.act (liftA (quditCasimir 3 (Fin 2))) (qutritCoupled r J) =
        ((J.val : ℂ) * ((J.val : ℂ) + 1)) • qutritCoupled r J) ∧
    (∀ (r : Fin 3) (i : Fin 2) (J K : Fin 3),
      ((qutritFrame r)ᴴ * portProjector (d := 3) i * qutritFrame r) J K =
        (1 / 9 : ℂ) * (if i = 0 then (-1 : ℂ) ^ (J.val + K.val) else 1) *
          (Real.sqrt (((2 * J.val + 1 : ℕ) : ℝ) * ((2 * K.val + 1 : ℕ) : ℝ)) : ℂ)) ∧
    (∀ r : Fin 3, (qutritFrame r)ᴴ * pbtRho 3 2 * qutritFrame r = qutritBlock) ∧
    pbtRho 3 2 = ∑ r : Fin 3, qutritFrame r * qutritBlock * (qutritFrame r)ᴴ ∧
    (1 - casimirProjector (totalCasimir 3 2) 2) * pbtRho 3 2 = 0 ∧
    liftA (quditCasimir 3 (Fin 2)) * pbtRho 3 2 ≠ pbtRho 3 2 * liftA (quditCasimir 3 (Fin 2)) ∧
    (pbtRho 3 2).charpoly = Polynomial.X ^ 21 *
      (Polynomial.X - Polynomial.C (4 / 9 : ℂ)) ^ 3 *
      (Polynomial.X - Polynomial.C (2 / 9 : ℂ)) ^ 3 ∧
    Module.finrank ℂ (LinearMap.ker (pbtRho 3 2).mulVecLin) = 21 ∧
    (∀ r : Fin 3, QAlgorithms.IsState (qutritKernelVector r) ∧
      QAlgorithms.act (pbtRho 3 2) (qutritKernelVector r) = 0) ∧
    1 - support (pbtRho 3 2) = 1 - casimirProjector (totalCasimir 3 2) 2 +
      ∑ r : Fin 3, QAlgorithms.pureDensity (qutritKernelVector r) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P53

end
