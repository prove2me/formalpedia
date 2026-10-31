-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P28_kl_tv_chi_bounds
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P28.kl_tv_chi_bounds
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T00:28:42.422314+00:00
-- url     : https://prove2.me/theorems/c049be04-9ace-4dfe-bad1-2ac4fe6e431b
-- title:
--   Theorem 2: D <= (c1 TV+c2 chi2) log e holds for (c1,c2)=(0,1),(1/4,1/2)
-- statement:
--   Fix logarithm base $b>1$ and write $\ell=\log_b e$. For all probability measures $P\ll Q$,
--
--   $$D(P\|Q)\le(c_1|P-Q|+c_2\chi^2(P\|Q))\ell$$
--
--   holds for $(c_1,c_2)=(0,1)$ and $(1/4,1/2)$. At $c_1=0$ the least possible $c_2$ is 1; at $c_2=1/2$ the least possible $c_1$ is $1/4$. Over mutually absolutely continuous pairs on all alphabets, the best coefficient comparing the symmetric KL sum to the symmetric chi-square sum is $\ell/2$. Here $|P-Q|$ denotes full L1 total variation. These are two distinct coordinatewise optimality assertions.
-- source:
--   $f$-divergence Inequalities, arXiv:1508.00335v7, PDF p. 15, Theorem 2

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P28

noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal NNReal Topology BigOperators ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P28

universe u

attribute [local instance] Classical.propDecidable

/-- Theorem 2: D <= (c1 TV+c2 chi2) log e holds for (c1,c2)=(0,1),(1/4,1/2). Sason--Verdu, arXiv:1508.00335v7, PDF p.15.  -/
theorem kl_tv_chi_bounds
    (b : LogBase) :
    KLLinearBound.{u} b 0 1 ∧ KLLinearBound.{u} b (1 / 4) (1 / 2) ∧
    IsLeast {c | KLLinearBound.{u} b 0 c} 1 ∧
    IsLeast {c | KLLinearBound.{u} b c (1 / 2)} (1 / 4) ∧
    Sharp (symmetricKL b) symmetricChi mutualPairs (ENNReal.ofReal (logBaseE b / 2)) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P28

end
