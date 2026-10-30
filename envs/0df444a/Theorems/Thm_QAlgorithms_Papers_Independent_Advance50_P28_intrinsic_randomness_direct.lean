-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P28_intrinsic_randomness_direct
-- name    : QAlgorithms.Papers.Independent.Advance50.P28.intrinsic_randomness_direct
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:50:24.04503+00:00
-- url     : https://prove2.me/theorems/cf403f1e-f2cf-45a6-9e9e-a21f2c4ea1e2
-- title:
--   Lemma 5 (58)
-- statement:
--   All logarithms are natural and $d_1$ is the full $L^1$ distance. Let $P$ be a normalized law on a finite nonempty alphabet $A$, and let $U_M$ be the uniform law on $M\ge1$ symbols. For a map $f$, write $f_*P$ for its pushforward. For $R\ge0$, put $M_n=\lfloor e^{nR}\rfloor$ and let $d_n$ be the minimum full $L^1$ error over all maps $A^n\to\{1,\ldots,M_n\}$. With $g(s)=-\log\sum_aP(a)^{1+s}$ and $g(0)=0$,
--   $$\liminf_n-\frac1n\log d_n\ge\max_{0\le s\le1}\{g(s)-sR\}.$$
--   Exact extraction gives $+\infty$ on the left. This retains the achievability inequality without importing the false equality assertion of Theorem 4.
-- source:
--   Tight exponential analysis of universally composable privacy amplification and its applications, arXiv:1010.1358v5, PDF p. 9, Lemma 5 (58)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P28

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology

namespace QAlgorithms.Papers.Independent.Advance50.P28

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Hayashi, PDF pp.9–10, Lemma 5, (58): achievability includes exact zero error. -/
theorem intrinsic_randomness_direct {A : Type*} [Fintype A] [Nonempty A]
    (P : A → ℝ) (hP : IsLaw P) (R : ℝ) (hR : 0 ≤ R) :
    (intrinsicExponent P R : EReal) ≤
      Filter.liminf (fun n => negativeLogRate (intrinsicExtractionError P R n) n) atTop := by sorry

end QAlgorithms.Papers.Independent.Advance50.P28

end
