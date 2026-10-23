-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P15_iWeight_rank_formula
-- name    : QAlgorithms.Papers.Independent.Renew46.P15.iWeight_rank_formula
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T20:17:30.580475+00:00
-- url     : https://prove2.me/theorems/97ee7db5-ab71-49c1-bf8d-4a0d357d92aa
-- title:
--   Normalized i-weight rank formula and enumeration
-- statement:
--   Fix $N\ge2$. Let $\mathcal S_N$ be the normalized dominant integral rows $S=(m_{1,N},\ldots,m_{N,N})$ with $m_{1,N}\ge\cdots\ge m_{N,N}=0$. Order them lexicographically, beginning with the first entry, and define $P(S)$ by counting the finitely many strictly smaller rows. Then
--
--   $$
--    P(S)=\sum_{k=1}^{N-1}\binom{N-k+m_{k,N}-1}{N-k}.
--   $$
--
--   Furthermore $P:\mathcal S_N\to\mathbb N$ is bijective and
--
--   $$
--    S<S^\prime\quad\Longleftrightarrow\quad P(S)<P(S^\prime).
--   $$
--
--   Thus $P$ is a zero-based enumeration of all normalized irrep labels at fixed rank. The sum's upper index is computed before subtracting one, including when an entry is zero.
-- source:
--   A numerical algorithm for the explicit calculation of SU(N) and SL(N,C) Clebsch-Gordan coefficients, arXiv:1009.0437v2, PDF p. 17, Appendix C.1, Eqs.(C1)–(C6)

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P15

noncomputable section

open scoped BigOperators Matrix

namespace QAlgorithms.Papers.Independent.Renew46.P15

attribute [local instance] Classical.propDecidable

/-- Appendix C.1, (C1)-(C6), PDF pp.16-17: the independent counting rank is
an order-preserving bijection with the nonnegative integers, with formula (C6).
N=n+2 excludes the false N=1 extension. -/
theorem iWeight_rank_formula (n : ℕ) :
    (∀ s : GTTopRow n, weightRank s = weightRankFormula s.val) ∧
    Function.Bijective (weightRank (n := n)) ∧
    ∀ a b : GTTopRow n, weightLt a.val b.val ↔ weightRank a < weightRank b := by sorry

end QAlgorithms.Papers.Independent.Renew46.P15

end
