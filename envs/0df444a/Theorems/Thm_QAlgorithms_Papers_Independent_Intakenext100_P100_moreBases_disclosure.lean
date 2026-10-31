-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P100_moreBases_disclosure
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P100.moreBases_disclosure
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:21:16.433524+00:00
-- url     : https://prove2.me/theorems/fa65d92f-4b78-49d7-8d10-a1ad0f2ee441
-- title:
--   L-basis disclosure and variational bound
-- statement:
--   Let $d\ge1$ and $L\ge2$ be integers, and let $U_t$ for $0\le t<L$ be unitary matrices with $U_0=I$ whose column bases are pairwise mutually unbiased. Let
--   $$\rho=\frac1{Ld}\sum_{k=0}^{d-1}\sum_{t=0}^{L-1}|k,t\rangle\langle k,t|_A\otimes U_t|k\rangle\langle k|U_t^\dagger{}_B.$$
--   Disclosing $t$, undoing $U_t$ and measuring $k$ produces the normalized shared-label state $\rho'$. Then
--   $$I_c(\rho')=\log_2L+\log_2d,$$
--   $$I_c(\rho)\le\log_2d+\max_{\|\phi\|=1}\frac1L\sum_{t,k}|\langle\phi|U_t|k\rangle|^2\log_2|\langle\phi|U_t|k\rangle|^2.$$
--   The maximum is attained, and zero-probability terms contribute zero. The disclosure uses exactly $L$ possible message labels, hence fits every integer budget $l$ with $L\le2^l$; $\log_2L$ is its entropy, not an asserted integer bit count. This is the variational starting point for locking with more bases.
-- source:
--   Locking classical correlation in quantum states, arXiv:quant-ph/0303088v1, PDF p. 5, Appendix, Eqs. (17)–(18)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P100

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P100

open QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.5, Eqs.(17)--(18): L-basis disclosure and the normalized variational
bound. log_2 L is key entropy, not an integer wire count. -/
theorem moreBases_disclosure (d L : ℕ) (hd : 0 < d) (hL : 2 ≤ L)
    (U : Fin L → Matrix.unitaryGroup (Fin d) ℂ) (hU : IsUnbiasedFamily U) :
    IsDensityMatrix (lockingState U) ∧ IsDensityMatrix (disclosedState d L) ∧
    lockingMeasuredInformation (disclosedState d L) = Real.logb 2 L + Real.logb 2 d ∧
    (∀ l : ℕ, L ≤ 2^l →
      ∃ P : OneWayMap (Fin d × Fin L) (Fin d) (Fin d × Fin L) (Fin d × Fin L) l,
        P.messages = L ∧ oneWayOutput P (lockingState U) = disclosedState d L) ∧
    lockingMeasuredInformation (lockingState U) ≤ Real.logb 2 d + maximalBasisScore U ∧
    (∃ phi : EuclideanSpace ℂ (Fin d), ‖phi‖ = 1 ∧
      maximalBasisScore U = basisScore U phi) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P100

end
