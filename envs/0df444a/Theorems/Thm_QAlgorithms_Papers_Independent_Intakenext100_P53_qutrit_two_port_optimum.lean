-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P53_qutrit_two_port_optimum
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P53.qutrit_two_port_optimum
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:34:29.596211+00:00
-- url     : https://prove2.me/theorems/339d3351-1bf7-4301-b550-9b5fdac30836
-- title:
--   Exact optimal qutrit two-port probabilistic protocol
-- statement:
--   For $d=3,N=2$, let $P_A(J)$ be the physical two-qutrit spin-$J$ projector. Define
--   $$X=\tfrac65P_A(0)+\tfrac35P_A(1)+\tfrac65P_A(2),\quad O=\sqrt X,\quad\widetilde\Pi_i=\tfrac9{10}P^-_{A_iC}\otimes I_{\bar A_i}.$$
--   Then $\operatorname{tr}X=9$, $OO^\dagger=X$, and $\sum_i\widetilde\Pi_i=(27/10)\rho\preceq X_A\otimes I_C$. The actual success effects satisfy
--   $$\Pi_i=(X_A\otimes I_C)^{-1/2}\widetilde\Pi_i(X_A\otimes I_C)^{-1/2}=\rho^{-1/2}\sigma_i\rho^{-1/2}.$$
--   Together with the full-space failure effect $I-\operatorname{supp}\rho$ they give exact probabilistic PBT. Each transformed success effect has trace $27/10$, and
--   $$p=\frac1{27}\sum_i\operatorname{tr}\widetilde\Pi_i=\frac15.$$
--   No normalized-resource exact probabilistic two-port qutrit protocol has greater success probability. Also $[\rho,O_A\otimes I_C]=0$.
--
--   This proves attainability here, without assuming optimality. The first factor in printed B6 is corrected from $10/9$ to $9/10$ as fixed by B5.
-- source:
--   Some remarks on port-based teleportation, arXiv:1506.01555v2, PDF p. 7, Appendix B Eqs.(B3)-(B6): exact qutrit two-port optimum and SRM

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P53

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P53

open scoped Classical ComplexConjugate ComplexOrder Matrix Matrix.Norms.L2Operator

-- Accepted generic matrix and positive-operator interfaces. The support is the
-- orthogonal range projection; all uses below are on positive physical rho.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Next46.P39 (inverseSqrt)

/-- PDF pp.6-7, Eqs.(B3)-(B6): exact optimum for d=3,N=2. Printed B6's
10/9 is corrected to 9/10 by B5. Failure uses the complete full-space kernel,
not the incomplete projector printed in B7. No optimality premise is assumed. -/
theorem qutrit_two_port_optimum :
    Matrix.trace qutritResourceSquare = 9 ∧
    qutritResource * qutritResourceᴴ = qutritResourceSquare ∧
    (∑ i : Fin 2, qutritTransformedEffect i) = (27 / 10 : ℂ) • pbtRho 3 2 ∧
    (liftA qutritResourceSquare - (27 / 10 : ℂ) • pbtRho 3 2).PosSemidef ∧
    (∀ i : Fin 2,
      inverseSqrt (liftA qutritResourceSquare) * qutritTransformedEffect i *
        inverseSqrt (liftA qutritResourceSquare) = srm 3 2 i ∧
      Matrix.trace (qutritTransformedEffect i) = 27 / 10) ∧
    ExactProbabilistic qutritResource (probabilisticSRM 3 2) ∧
    pbtSuccessProbability qutritResource (probabilisticSRM 3 2) = 1 / 5 ∧
    (∀ (O : Op (Ports 3 2)) (E : Option (Fin 2) → Op (AC 3 2)),
      ExactProbabilistic O E → pbtSuccessProbability O E ≤ 1 / 5) ∧
    pbtRho 3 2 * liftA qutritResource = liftA qutritResource * pbtRho 3 2 := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P53

end
