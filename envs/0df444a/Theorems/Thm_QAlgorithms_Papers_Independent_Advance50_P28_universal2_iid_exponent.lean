-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P28_universal2_iid_exponent
-- name    : QAlgorithms.Papers.Independent.Advance50.P28.universal2_iid_exponent
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T10:46:31.825899+00:00
-- url     : https://prove2.me/theorems/09f85075-b771-4ac8-ac9c-af725ade66ff
-- title:
--   IID universal2 direct exponent (18)
-- statement:
--   All logarithms are natural and $d_1$ is the full $L^1$ distance. Let $P$ be a normalized law on a finite nonempty alphabet $A$, and let $U_M$ be the uniform law on $M\ge1$ symbols. For a map $f$, write $f_*P$ for its pushforward. Let $P^n$ be the iid law, let $M_n\ge1$ satisfy $\log M_n/n\to R$, and let each source-independent ensemble $f_{X,n}:A^n\to\{1,\ldots,M_n\}$ be universal2. Write $g(s)=-\log\sum_aP(a)^{1+s}$, $g(0)=0$. Then
--   $$\liminf_{n\to\infty}-\frac1n\log\mathbb E_Xd_1(f_{X,n*}P^n,U_{M_n})\ge\max_{0\le s\le1}\frac{g(s)-sR}{1+s}.$$
--   Zero error has exponent $+\infty$. This is the direct bound, with no converse or unconditional tightness assertion.
-- source:
--   Tight exponential analysis of universally composable privacy amplification and its applications, arXiv:1010.1358v5, PDF p. 4, IID universal2 direct exponent (18)

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P28

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology

namespace QAlgorithms.Papers.Independent.Advance50.P28

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Hayashi, PDF p.4, (18): general direct exponent, with infinite exact-extraction rates. -/
theorem universal2_iid_exponent {A : Type*} [Fintype A] [Nonempty A]
    (P : A → ℝ) (hP : IsLaw P) (M : ℕ → ℕ) (hM : ∀ n, 0 < M n)
    (h : (n : ℕ) → HashEnsemble (Fin n → A) (M n)) (hu : ∀ n, Universal2 (h n))
    (R : ℝ) (hrate : Tendsto (fun n => Real.log (M n : ℝ) / (n : ℝ)) atTop (𝓝 R)) :
    (directExponent P R : EReal) ≤
      Filter.liminf (fun n => negativeLogRate (expectedError (h n) (iid P n)) n) atTop := by sorry

end QAlgorithms.Papers.Independent.Advance50.P28

end
