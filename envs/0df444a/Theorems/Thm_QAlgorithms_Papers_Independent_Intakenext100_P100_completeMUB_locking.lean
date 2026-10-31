-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P100_completeMUB_locking
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P100.completeMUB_locking
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:21:57.38135+00:00
-- url     : https://prove2.me/theorems/ce4760e8-b04b-40a6-b890-ebaa5b4bea37
-- title:
--   Complete mutually unbiased bases locking bounds
-- statement:
--   Let $d\ge2$ and supply $d+1$ pairwise mutually unbiased unitary bases of $\mathbb C^d$, with $U_0=I$. Let $\rho$ be their uniform locking state and $\rho'$ the decoded shared-label state after the basis label is disclosed. Both are density matrices. Then
--   $$I_c(\rho)\le\log_2d-\log_2(d+1)+1=1-\log_2(1+1/d),$$
--   $$I_c(\rho')-I_c(\rho)\ge2\log_2(d+1)-1.$$
--   These are upper and lower bounds, respectively. They do not assert an exact initial correlation or existence of a complete family in every dimension.
-- source:
--   Locking classical correlation in quantum states, arXiv:quant-ph/0303088v1, PDF p. 5, Appendix, complete L=d+1 family

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P100

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P100

open QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.5: complete d+1 mutually unbiased bases give two bounds, not an
exact formula for I_c. Existence of a complete family is not assumed for
all d: the family is supplied explicitly. -/
theorem completeMUB_locking (d : ℕ) (hd : 2 ≤ d)
    (U : Fin (d+1) → Matrix.unitaryGroup (Fin d) ℂ) (hU : IsUnbiasedFamily U) :
    IsDensityMatrix (lockingState U) ∧ IsDensityMatrix (disclosedState d (d+1)) ∧
    lockingMeasuredInformation (lockingState U) ≤
      Real.logb 2 d - Real.logb 2 (d+1) + 1 ∧
    Real.logb 2 d - Real.logb 2 (d+1) + 1 =
      1 - Real.logb 2 (1 + 1 / (d : ℝ)) ∧
    lockingMeasuredInformation (disclosedState d (d+1)) - lockingMeasuredInformation (lockingState U) ≥
      2 * Real.logb 2 (d+1) - 1 := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P100

end
