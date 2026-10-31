-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P66_constrainedEntropyFamily_prime
-- name    : QAlgorithms.Papers.Independent.Intake100.P66.constrainedEntropyFamily_prime
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:15:54.065918+00:00
-- url     : https://prove2.me/theorems/090e4590-f703-4886-af62-1a48960967e2
-- title:
--   The purified variant for arbitrary mixed states
-- statement:
--   Let $n\ge1$ be an integer. Let $\rho$ be a density operator (positive semidefinite with trace one) on the tensor product of distinct finite-dimensional complex systems $A,B,C,X_1,\ldots,X_n$, each of positive dimension; dimension one is allowed. For any subsystem $J$, let $S(J)=S(\operatorname{Tr}_{J^c}\rho)$ be its von Neumann entropy in bits, with $S(\varnothing)=0$ and $0\log0=0$. For disjoint subsystems, write $I(U:V)=S(U)+S(V)-S(UV)$ and $I(U:V\mid W)=S(UW)+S(VW)-S(W)-S(UVW)$. Assume
--   $$I(A:C\mid B)=I(B:C\mid A)=0.$$
--
--   Then
--   $$\sum_{i=1}^n I(A:B\mid X_i)+\sum_{i=1}^n S(X_i)+I(A:B\mid CX_1\cdots X_n)+S(ABCX_1\cdots X_n)-S(ABC)-nI(AB:C)\ge0.$$
--   This is the entropy inequality obtained by eliminating a purifying party. No purity assumption is imposed on $\rho$.
-- source:
--   Infinitely many constrained inequalities for the von Neumann entropy, arXiv:1107.0624v1, PDF p. 9, Theorem 1′, §V, equation (46): purified variant

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P66

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P66

open scoped BigOperators

open QAlgorithms (IsDensityMatrix vnEntropy)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.9, Theorem 1-prime, (45)--(46): arbitrary mixed states; both S(total)
and -S(ABC) remain, with coefficient n on I(AB:C). -/
theorem constrainedEntropyFamily_prime (n : ℕ) (hn : 1 ≤ n) (d : entropyParty n → ℕ)
    (hd : ∀ j, 0 < d j) (rho : Matrix (entropyProductBasis d) (entropyProductBasis d) ℂ)
    (hrho : IsDensityMatrix rho)
    (hAC : evaluateEntropyForm (cmiForm {entropyLabelA} {c} {b}) (entropyOfSubset d rho) = 0)
    (hBC : evaluateEntropyForm (cmiForm {b} {c} {entropyLabelA}) (entropyOfSubset d rho) = 0) :
    0 ≤ evaluateEntropyForm (primeForm {entropyLabelA} {b} {c} standardX) (entropyOfSubset d rho) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P66

end
