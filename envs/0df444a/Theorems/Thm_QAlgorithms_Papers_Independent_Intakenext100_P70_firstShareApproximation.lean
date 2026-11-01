-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P70_firstShareApproximation
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P70.firstShareApproximation
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:42:10.993747+00:00
-- url     : https://prove2.me/theorems/b40ec902-6c29-4b5c-8d25-069afcca7399
-- title:
--   The first shield share is close to a perfect private bit
-- statement:
--   Let $N,m\geq1$ and $d\geq2$ be integers. Set $q=1/3$ and $r=2m+\lceil\log_2m\rceil$, and construct the normalized state $\zeta^{abAB}$ in (S18) on the qubit key $ab$ and the $N$ shield shares. Write
--   $$
--   \rho^{abA_1B_1}=\operatorname{Tr}_{A_2B_2\cdots A_NB_N}\zeta^{abAB}.
--   $$
--   There is a perfect private bit $\gamma^{abA_1B_1}$ such that
--   $$
--   \|\rho^{abA_1B_1}-\gamma^{abA_1B_1}\|_1\leq16\sqrt m\,2^{-m/4}.
--   $$
--   Here $\|X\|_1=\operatorname{Tr}\sqrt{X^\dagger X}$ is the full trace norm. A perfect private bit is a normalized state obtained by applying a key-controlled twisting unitary to a Bell pair on $ab$ tensored with an arbitrary shield density matrix.
--
--   This approximation concerns the computed first-share marginal and does not require the PPT condition (S19).
-- source:
--   Unbounded number of channel uses are required to see quantum capacity, arXiv:1408.5115v1, PDF p. 7, Supplementary Lemma 2; Eq. (S20), proof p.8

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P70

namespace QAlgorithms.Papers.Independent.Intakenext100.P70

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P22
  (Op coherentInformation singleUseInformation quantumCapacity mixed)

/-- Supplementary Lemma 2, PDF pp.7--8: the S20 first-share marginal is close to a perfect
private bit. No PPT hypothesis is needed. The proof covers m>5 quantitatively; for positive
m<=5 its stated bound exceeds 2, the universal full trace-distance bound. -/
theorem firstShareApproximation (N m d : ℕ) (hN : 0 < N) (hm : 0 < m) (hd : 2 ≤ d) :
    let P := cubittApproximationParameters N m d
    ∃ rho : Op ((Bool × CubittShare P.r P.m P.d) × (Bool × CubittShare P.r P.m P.d)),
      CubittPerfectPbit rho ∧ traceNorm (cubittFirstShareState P hN - rho) ≤ cubittApproximationBound m := by sorry

end

end QAlgorithms.Papers.Independent.Intakenext100.P70
