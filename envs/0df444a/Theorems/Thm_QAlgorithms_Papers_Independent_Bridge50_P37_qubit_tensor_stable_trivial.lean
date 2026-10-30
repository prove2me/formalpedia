-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P37_qubit_tensor_stable_trivial
-- name    : QAlgorithms.Papers.Independent.Bridge50.P37.qubit_tensor_stable_trivial
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:36:48.987502+00:00
-- url     : https://prove2.me/theorems/2c42fc8b-2862-4a59-8ee9-761b31a9ecb7
-- title:
--   Theorem 2: no nontrivial tensor-stable map with a qubit input or output
-- statement:
--   Write $M_d$ for complex $d\times d$ matrices in fixed orthonormal bases; positive means positive semidefinite. All maps are complex-linear and all dimensions are positive integers. CP means completely positive, coCP means that output transposition composed with the map is CP, and nontrivial means neither. Tensor-stable positivity means positivity at every positive tensor degree.
--
--   For every $d\ge1$, every tensor-stable positive map in either orientation satisfies
--   $$P:M_2\to M_d\ \text{or}\ P:M_d\to M_2\quad\Longrightarrow\quad P\text{ is CP or coCP}.$$
--   Both orientations are asserted, including $d=1$. The two trivial cones need not coincide.
-- source:
--   Positivity of linear maps under tensor powers, arXiv:1502.05630v2, PDF p. 3, Theorem 2: no nontrivial tensor-stable map with a qubit input or output

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

/-- Theorem 2, PDF pp.3,18: both qubit orientations, including scalar opposite dimension. -/
theorem qubit_tensor_stable_trivial (d : ℕ) [NeZero d] :
    (∀ P : MatrixMap (Fin 2) (Fin d), TensorStable P →
      Entanglement.IsCompletelyPositive P ∨ OutputCoPositive P) ∧
    (∀ P : MatrixMap (Fin d) (Fin 2), TensorStable P →
      Entanglement.IsCompletelyPositive P ∨ OutputCoPositive P) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P37

end
