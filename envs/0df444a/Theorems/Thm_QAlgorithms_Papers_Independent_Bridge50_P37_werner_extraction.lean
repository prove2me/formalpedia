-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P37_werner_extraction
-- name    : QAlgorithms.Papers.Independent.Bridge50.P37.werner_extraction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:55:20.827755+00:00
-- url     : https://prove2.me/theorems/2b1e5b1b-4405-49e4-8b64-06d6b0084eae
-- title:
--   Lemma 7: extraction of entangled Werner states from positive maps
-- statement:
--   Write $M_d$ for complex $d\times d$ matrices in fixed orthonormal bases; positive means positive semidefinite. All maps are complex-linear and all dimensions are positive integers. CP means completely positive, coCP means that output transposition composed with the map is CP, and nontrivial means neither. Tensor-stable positivity means positivity at every positive tensor degree. The symbols $\|\cdot\|_\diamond$, $\|\cdot\|_1$ and $\|\cdot\|_\infty$ denote the diamond, trace and spectral norms, respectively; $*$ denotes the Hilbert--Schmidt adjoint. Choi matrices and maximally entangled projections use the normalized, reference-first convention.
--
--   Let $P:M_{d_1}\to M_{d_2}$ be positive and not coCP. For each $d\in\{d_1,d_2\}$ there exist a separable CP map $S:M_{d_1}\otimes M_{d_2}\to M_d\otimes M_d$ and $p\in[-1,0)$ such that
--   $$S(C_P)=\rho_{W,d}^{(p)},\qquad \rho_{W,d}^{(p)}\text{ is a normalized entangled Werner state}.$$
--   The parameter $p$ is the flip expectation. The input $C_P$ is only block-positive; positivity and trace one of the output are conclusions. $S$ is not required to preserve trace.
-- source:
--   Positivity of linear maps under tensor powers, arXiv:1502.05630v2, PDF p. 17, Lemma 7: extraction of entangled Werner states from positive maps

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

/-- Lemma 7, PDF pp.17--18: the Choi input need only be block-positive. Positivity,
normalization and entanglement of the extracted Werner state are conclusions. -/
theorem werner_extraction (d1 d2 d : ℕ) [NeZero d1] [NeZero d2]
    (P : MatrixMap (Fin d1) (Fin d2)) (hP : IsPositiveMap P) (hnco : ¬ OutputCoPositive P)
    (hd : d = d1 ∨ d = d2) :
    ∃ S : MatrixMap (Fin d1 × Fin d2) (Fin d × Fin d), ∃ p : ℝ,
      SeparableMap S ∧ -1 ≤ p ∧ p < 0 ∧ S (normalizedChoi P) = flipParamWernerState d p ∧
      IsDensityMatrix (S (normalizedChoi P)) ∧ ¬ Entanglement.IsSeparablePositive (S (normalizedChoi P)) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P37

end
