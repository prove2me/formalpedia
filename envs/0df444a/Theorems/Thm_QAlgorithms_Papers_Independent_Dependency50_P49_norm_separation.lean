-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P49_norm_separation
-- name    : QAlgorithms.Papers.Independent.Dependency50.P49.norm_separation
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T18:21:57.790607+00:00
-- url     : https://prove2.me/theorems/446121fd-8fb5-48d4-aa04-b423905a2a76
-- title:
--   Quantitative operator/cb separation near maximally mixed depolarization
-- statement:
--   For each positive integer $n$, let $S_n(X)=\operatorname{tr}(X)I/n$, let $\Theta_n$ be transpose, and put $T_n=\frac n{n+1}S_n+\frac1{n+1}\Theta_n$. These are Heisenberg quantum channels, and
--
--   $$\|T_n-S_n\|_{\infty\to\infty}\leq\frac2{n+1},\qquad \|T_n-S_n\|_{\rm cb}\geq\frac{n-1}{n+1},\qquad\lim_{n\to\infty}\|T_n-S_n\|_{\infty\to\infty}=0.$$
--
--   The first norm is the induced operator-to-operator norm, and the cb-norm stabilizes that norm over all finite reference systems. Neither has a factor of one half. The numerators and denominators are real arithmetic. This gives asymptotic separation near depolarization without claiming an exact cb-distance.
-- source:
--   The Information-Disturbance Tradeoff and the Continuity of Stinespring's Representation, arXiv:quant-ph/0605009v1, PDF p. 13, §V, Eqs. (44)–(47)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P49

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Kronecker Topology ENNReal

open Filter

open QAlgorithms.Papers.Independent.Information100.P75 (Mat)

open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap)

open QAlgorithms.Papers.Independent.Information100.P50 (coefficientMap)

open QAlgorithms.Papers.Independent.Information100.P08 (maximallyMixed)

namespace QAlgorithms.Papers.Independent.Dependency50.P49

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- The accepted all-Schatten norms at p=top are exactly the source's operator norms.

local notation "inducedNorm" => QAlgorithms.Papers.Independent.Information100.P50.inducedNorm (⊤ : ℝ≥0∞)

local notation "cbNorm" => QAlgorithms.Papers.Independent.Information100.P50.cbNorm (⊤ : ℝ≥0∞)

/-- PDF pp.12–13, (44)–(47): quantitative separation near maximally mixed
replacement. The p.12 heuristic cb>=1 is not asserted at finite n.
The n-1 numerator is real subtraction, including n=1. -/
theorem norm_separation :
    (∀ n : ℕ, 0 < n →
      IsQuantumChannel (transposeMixture n (1 / ((n : ℝ) + 1))) ∧
      inducedNorm (transposeMixture n (1 / ((n : ℝ) + 1)) - uniformDepolarizing n) ≤
        2 / ((n : ℝ) + 1) ∧
      ((n : ℝ) - 1) / ((n : ℝ) + 1) ≤
        cbNorm (transposeMixture n (1 / ((n : ℝ) + 1)) - uniformDepolarizing n)) ∧
    Tendsto (fun k : ℕ => inducedNorm
      (transposeMixture (k + 1) (1 / (((k + 1 : ℕ) : ℝ) + 1)) -
        uniformDepolarizing (k + 1))) atTop (𝓝 0) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P49

end
