-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P28_smoothing_benchmark_iid_exponent
-- name    : QAlgorithms.Papers.Independent.Advance50.P28.smoothing_benchmark_iid_exponent
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:47:36.192662+00:00
-- url     : https://prove2.me/theorems/acdf500a-c32f-401b-884f-ae042d42b735
-- title:
--   Smooth min-entropy IID evaluation (36)–(37)
-- statement:
--   All logarithms are natural and $d_1$ is the full $L^1$ distance. Let $P$ be a normalized law on a finite nonempty alphabet $A$, and let $U_M$ be the uniform law on $M\ge1$ symbols. For a map $f$, write $f_*P$ for its pushforward. For $R\ge0$, define the smoothing benchmark by minimizing over all subdistributions on $A^n$:
--   $$B_n(R)=\inf_Q\left[e^{nR/2}\sqrt{\max_xQ(x)}+2\|P^n-Q\|_1\right].$$
--   Write $g(s)=-\log\sum_aP(a)^{1+s}$, $g(0)=0$, and $H_\infty(P)=-\log\max_aP(a)$. Then
--   $$\lim_n-\frac{\log B_n(R)}n=\sup_{s\ge0}\frac{g(s)-sR}{1+2s}=\max_{0\le t\le1}\frac{tH_{1/(1-t)}(P)-tR}{1+t}.$$
--   The objective is zero at $t=0$ and $(H_\infty(P)-R)/2$ at $t=1$. Every universal2 sequence with $\log M_n/n\to R$ has expected-error liminf exponent at least this value, as in (36). This evaluates the smoothing method, rather than the optimal extractor. For $s>0$, $H_{1+s}(P)=-s^{-1}\log\sum_aP(a)^{1+s}$, and $g(s)=sH_{1+s}(P)$ with $g(0)=0$.
-- source:
--   Tight exponential analysis of universally composable privacy amplification and its applications, arXiv:1010.1358v5, PDF p. 7, Smooth min-entropy IID evaluation (36)–(37)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P28

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology

namespace QAlgorithms.Papers.Independent.Advance50.P28

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Hayashi, PDF p.7, (36)–(37), Appendix C p.18: exponent of the smoothing
BENCHMARK. The exact clipping objective is used, not the erroneous equality in (100). -/
theorem smoothing_benchmark_iid_exponent {A : Type*} [Fintype A] [Nonempty A]
    (P : A → ℝ) (hP : IsLaw P) (R : ℝ) (hR : 0 ≤ R)
    (M : ℕ → ℕ) (hM : ∀ n, 0 < M n)
    (h : (n : ℕ) → HashEnsemble (Fin n → A) (M n)) (hu : ∀ n, Universal2 (h n))
    (hrate : Tendsto (fun n => Real.log (M n : ℝ) / (n : ℝ)) atTop (𝓝 R)) :
    Tendsto (fun n => negativeLogRate (smoothingBenchmark P R n) n) atTop
      (𝓝 (smoothExponent P R : EReal)) ∧
    smoothExponent P R = sSup (compactSmoothObjective P R '' Set.Icc 0 1) ∧
    (smoothExponent P R : EReal) ≤
      Filter.liminf (fun n => negativeLogRate (expectedError (h n) (iid P n)) n) atTop := by sorry

end QAlgorithms.Papers.Independent.Advance50.P28

end
