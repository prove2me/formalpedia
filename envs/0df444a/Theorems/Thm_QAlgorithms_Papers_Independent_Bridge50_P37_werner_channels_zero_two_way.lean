-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P37_werner_channels_zero_two_way
-- name    : QAlgorithms.Papers.Independent.Bridge50.P37.werner_channels_zero_two_way
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:53:24.482461+00:00
-- url     : https://prove2.me/theorems/6c1bfcd5-b874-4575-ae82-1527caac7722
-- title:
--   Unnumbered application: nontrivial tensor-stable maps force NPPT Werner channels of zero two-way capacity
-- statement:
--   Write $M_d$ for complex $d\times d$ matrices in fixed orthonormal bases; positive means positive semidefinite. All maps are complex-linear and all dimensions are positive integers. CP means completely positive, coCP means that output transposition composed with the map is CP, and nontrivial means neither. Tensor-stable positivity means positivity at every positive tensor degree.
--
--   Suppose a nontrivial tensor-stable positive map $M_{d_1}\to M_{d_2}$ exists. For each choice $d\in\{d_1,d_2\}$, necessarily $d>2$, and there exists $p_0\in[-1,0)$ such that
--   $$\forall p\in[p_0,0):\quad W_{d,p}\text{ is a channel},\quad Q_2(W_{d,p})=0,\quad W_{d,p}\text{ is not coCP}.$$
--   Here $W_{d,p}$ is Eq. (2). Its normalized Choi state is the NPPT Werner state with flip expectation $p$. Both local dimensions and the entire parameter interval are retained. The source's separate antidegradability observation is background, rather than an unconditional new zero-capacity construction.
-- source:
--   Positivity of linear maps under tensor powers, arXiv:1502.05630v2, PDF p. 16, Unnumbered application: nontrivial tensor-stable maps force NPPT Werner channels of zero two-way capacity

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

/-- Unnumbered Werner-channel application, PDF p.16, with extraction pp.18--19.
For each local dimension the entire parameter interval [p0,0) has zero Q2. -/
theorem werner_channels_zero_two_way (d1 d2 : ℕ) [NeZero d1] [NeZero d2]
    (h : ∃ P : MatrixMap (Fin d1) (Fin d2), TensorStable P ∧ Nontrivial P) :
    ∀ d : ℕ, (d = d1 ∨ d = d2) → 2 < d ∧
      ∃ p0 : ℝ, -1 ≤ p0 ∧ p0 < 0 ∧ ∀ p : ℝ, p0 ≤ p → p < 0 →
        IsChannel (wernerMap d p) ∧ diamondAssistedCapacity (wernerMap d p) false = 0 ∧
        ¬ OutputCoPositive (wernerMap d p) ∧
        IsDensityMatrix (flipParamWernerState d p) ∧ ¬ (gamma (flipParamWernerState d p)).PosSemidef := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P37

end
