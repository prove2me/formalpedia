-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P37_reduction_criterion_extraction
-- name    : QAlgorithms.Papers.Independent.Bridge50.P37.reduction_criterion_extraction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:56:48.91832+00:00
-- url     : https://prove2.me/theorems/53223b95-46e3-4b94-afd2-7fb2766f9375
-- title:
--   Lemma 8: two orientations of the reduction criterion
-- statement:
--   Write $M_d$ for complex $d\times d$ matrices in fixed orthonormal bases; positive means positive semidefinite. All maps are complex-linear and all dimensions are positive integers. CP means completely positive, coCP means that output transposition composed with the map is CP, and nontrivial means neither. Tensor-stable positivity means positivity at every positive tensor degree. The symbols $\|\cdot\|_\diamond$, $\|\cdot\|_1$ and $\|\cdot\|_\infty$ denote the diamond, trace and spectral norms, respectively; $*$ denotes the Hilbert--Schmidt adjoint. Choi matrices and maximally entangled projections use the normalized, reference-first convention.
--
--   Let $P:M_{d_1}\to M_{d_2}$ be positive and $\Gamma_d(X)=\operatorname{tr}(X)I_d-X$. Both implications hold:
--   $$\Gamma_{d_2}\circ P\text{ not CP}\ \Longrightarrow\ \exists S\text{ separable CP}:\ S(C_P)=\rho_{I,d_2}^{(p)},\quad 1/d_2<p\le1,$$
--   $$P\circ\Gamma_{d_1}\text{ not CP}\ \Longrightarrow\ \exists S\text{ separable CP}:\ S(C_P)=\rho_{I,d_1}^{(p)},\quad 1/d_1<p\le1.$$
--   In the first case $S$ has output $M_{d_2}\otimes M_{d_2}$, and in the second $M_{d_1}\otimes M_{d_1}$. In both cases its input is $M_{d_1}\otimes M_{d_2}$ and its output is a normalized entangled isotropic state; $p=\operatorname{tr}(\rho_I\omega_d)$ is the maximally entangled overlap.
-- source:
--   Positivity of linear maps under tensor powers, arXiv:1502.05630v2, PDF p. 19, Lemma 8: two orientations of the reduction criterion

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

/-- Lemma 8, PDF pp.19--20: both orientations and their different output dimensions. -/
theorem reduction_criterion_extraction (d1 d2 : ℕ) [NeZero d1] [NeZero d2]
    (P : MatrixMap (Fin d1) (Fin d2)) (hP : IsPositiveMap P) :
    (¬ Entanglement.IsCompletelyPositive ((reductionMap (Fin d2)).comp P) →
      ∃ S : MatrixMap (Fin d1 × Fin d2) (Fin d2 × Fin d2), ∃ p : ℝ,
        SeparableMap S ∧ (1 : ℝ)/d2 < p ∧ p ≤ 1 ∧ S (normalizedChoi P) = isotropicState d2 p ∧
        IsDensityMatrix (S (normalizedChoi P)) ∧ ¬ Entanglement.IsSeparablePositive (S (normalizedChoi P))) ∧
    (¬ Entanglement.IsCompletelyPositive (P.comp (reductionMap (Fin d1))) →
      ∃ S : MatrixMap (Fin d1 × Fin d2) (Fin d1 × Fin d1), ∃ p : ℝ,
        SeparableMap S ∧ (1 : ℝ)/d1 < p ∧ p ≤ 1 ∧ S (normalizedChoi P) = isotropicState d1 p ∧
        IsDensityMatrix (S (normalizedChoi P)) ∧ ¬ Entanglement.IsSeparablePositive (S (normalizedChoi P))) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P37

end
