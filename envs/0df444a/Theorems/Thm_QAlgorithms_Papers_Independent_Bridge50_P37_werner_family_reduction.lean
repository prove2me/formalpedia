-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P37_werner_family_reduction
-- name    : QAlgorithms.Papers.Independent.Bridge50.P37.werner_family_reduction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:37:44.64617+00:00
-- url     : https://prove2.me/theorems/16d16115-7c1a-43e3-9634-0b180a0208f0
-- title:
--   Theorem 3: one-parameter Werner family reduction, both directions
-- statement:
--   Write $M_d$ for complex $d\times d$ matrices in fixed orthonormal bases; positive means positive semidefinite. All maps are complex-linear and all dimensions are positive integers. CP means completely positive, coCP means that output transposition composed with the map is CP, and nontrivial means neither. Tensor-stable positivity means positivity at every positive tensor degree.
--
--   Let $d_1,d_2\ge1$, and choose either $d=d_1$ or $d=d_2$ with $d\ge2$. Put
--   $$W_{d,p}(X)=\frac{(d-p)\operatorname{tr}(X)I_d-(1-dp)X^T}{d^2-1},\qquad P_{d,p}=W_{d,p}\otimes(\vartheta_d\circ W_{d,p}).$$
--   If a nontrivial tensor-stable positive map $M_{d_1}\to M_{d_2}$ exists, then
--   $$\exists p\in[-1,0):\quad P_{d,p}\text{ is tensor-stable positive}.$$
--   Conversely, for each $p\in[-1,0)$, tensor-stable positivity of $P_{d,p}$ implies that it is neither CP nor coCP. The reduction applies separately to each choice of $d$; the candidate is not asserted to be a channel.
-- source:
--   Positivity of linear maps under tensor powers, arXiv:1502.05630v2, PDF p. 3, Theorem 3: one-parameter Werner family reduction, both directions

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P37

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

-- Only the following exact definition bodies are reused from pinned accepted papers.

open QAlgorithms.Papers.Independent.Information100.P04 (gamma copies)

open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap IsPositiveMap)

open QAlgorithms.Papers.Independent.Information100.P50 (maxEigenvalue)

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Information100.P69 (diamond)

open QAlgorithms.Papers.Independent.Information100.P56 (normalizedChoi)

open QAlgorithms.Papers.Independent.Information100.P76 (swapMatrix)

open QAlgorithms.Papers.Independent.Next46.P39 (inverseSqrt)

namespace QAlgorithms.Papers.Independent.Bridge50.P37

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

/-- Theorem 3, PDF pp.3,18--19: both directions, for EACH chosen local dimension.
The Werner formulas are used only for d>=2, excluding their scalar zero denominator. -/
theorem werner_family_reduction (d1 d2 d : ℕ) [NeZero d1] [NeZero d2]
    (hd : 2 ≤ d) (hchoice : d = d1 ∨ d = d2) :
    ((∃ P : MatrixMap (Fin d1) (Fin d2), TensorStable P ∧ Nontrivial P) →
      ∃ p : ℝ, -1 ≤ p ∧ p < 0 ∧ TensorStable (candidateMap d p)) ∧
    (∀ p : ℝ, -1 ≤ p → p < 0 → TensorStable (candidateMap d p) →
      Nontrivial (candidateMap d p)) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P37

end
