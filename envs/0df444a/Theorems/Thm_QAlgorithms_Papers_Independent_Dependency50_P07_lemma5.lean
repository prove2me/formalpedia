-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P07_lemma5
-- name    : QAlgorithms.Papers.Independent.Dependency50.P07.lemma5
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:27:31.638192+00:00
-- url     : https://prove2.me/theorems/2cb44e2a-8460-47d4-9e4d-f6a13c7e11eb
-- title:
--   Entropy bound from a high-probability effect
-- statement:
--   Let $\sigma$ be a density matrix on a nonzero finite-dimensional complex Hilbert space of dimension $D$. Let $B$ satisfy $0\le B\le I$, and suppose $\operatorname{Tr}(\sigma B)=1-\epsilon$. Then
--
--   $$H(\sigma)\le1+\epsilon\log_2D+(1-\epsilon)\log_2(\operatorname{Tr}B+1).$$
--
--   The density and effect conditions already imply $0\le\epsilon\le1$; neither endpoint is excluded. This bound controls entropy using an effect that accepts with high probability.
-- source:
--   Distilling common randomness from bipartite quantum states, arXiv:quant-ph/0304196v2, PDF p. 9, Lemma 5: entropy controlled by a high-probability effect

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P07

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder

open Filter

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Information100.P04 (Measurement)

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Dependency50.P07

/-- PDF p.9, Lemma 5: density and effect hypotheses force epsilon into [0,1], including both
endpoints. Traces are real parts and the dimension is strictly positive. -/
theorem lemma5 {Q : Type} [Fintype Q] [DecidableEq Q] [Nonempty Q]
    (sigma B : Matrix Q Q ℂ) (hsigma : IsDensityMatrix sigma) (hB : IsEffect B)
    (epsilon : ℝ) (htrace : (sigma * B).trace.re = 1 - epsilon) :
    vnEntropy sigma ≤ 1 + epsilon * Real.logb 2 (Fintype.card Q) +
      (1 - epsilon) * Real.logb 2 (B.trace.re + 1) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P07

end
