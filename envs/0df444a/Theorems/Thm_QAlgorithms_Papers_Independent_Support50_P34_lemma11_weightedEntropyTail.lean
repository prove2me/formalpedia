-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P34_lemma11_weightedEntropyTail
-- name    : QAlgorithms.Papers.Independent.Support50.P34.lemma11_weightedEntropyTail
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:52:53.411726+00:00
-- url     : https://prove2.me/theorems/f7875cc8-a6bd-486e-8160-34d0733774c9
-- title:
--   Lemma 11: weighted entropy-tail limit
-- statement:
--   Let $(h_j)_{j\ge1}$ be a nondecreasing sequence of strictly positive real numbers with finite convergence exponent
--
--   $$g(h)=\inf\left\{\lambda>0:\sum_{j\ge1}e^{-\lambda h_j}<\infty\right\}<\infty.$$
--
--   Let $B_1=\{x_j\ge0:\sum_jx_j\le1\}$ be the positive part of the real $\ell^1$ unit ball, and put $\eta(x)=-x\log x$, $\eta(0)=0$. Then
--
--   $$\lim_{m\to\infty}\sup_{x\in B_1}\sum_{j\ge m}\frac{\eta(x_j)}{h_j}=g(h).$$
--
--   Infima, suprema and sums retain nonnegative extended values. This is the scalar weighted entropy-tail limit. **Formalization Note** All sequence indices are shifted together to start at zero; source tail $j\ge m$ becomes zero-based tail $j\ge m-1$.
-- source:
--   Continuity of the von Neumann entropy, arXiv:0904.1963v3, PDF p. 38, Lemma 11: weighted entropy-tail limit

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P34

noncomputable section

open Filter MeasureTheory

open scoped ENNReal NNReal BigOperators

namespace QAlgorithms.Papers.Independent.Support50.P34

open QAlgorithms.Papers.Independent.Dependency50.P13
  (State PositiveTraceClass traceNormValue stateTraceNormTopology traceNormTopology
   operatorTrace IsPositive IsTraceClass stateEntropy relativeEntropy entropyWeight)

open QAlgorithms.Papers.Independent.Dependency50.P25 (extendedIntegral)

open QAlgorithms.Papers.Independent.Frontier18.P01 (binaryEntropy)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma 11, arXiv:0904.1963v3, PDF p.38: exact weighted entropy-tail limit.
All indices are shifted together by one from the source's positive indexing. -/
theorem lemma11_weightedEntropyTail (h : ℕ → ℝ) (hmono : Monotone h)
    (hpos : ∀ j, 0 < h j) (hfinite : convergenceExponent h < ⊤) :
    Tendsto (weightedEntropyTail h) atTop (nhds (convergenceExponent h)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P34

end
