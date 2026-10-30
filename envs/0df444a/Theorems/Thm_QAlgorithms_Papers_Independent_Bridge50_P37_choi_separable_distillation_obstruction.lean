-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P37_choi_separable_distillation_obstruction
-- name    : QAlgorithms.Papers.Independent.Bridge50.P37.choi_separable_distillation_obstruction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:54:20.977917+00:00
-- url     : https://prove2.me/theorems/effcd8e0-06f4-4ad5-a2b8-3db881c0bf7a
-- title:
--   Corollary 3: Choi-state separable-distillation obstruction
-- statement:
--   Write $M_d$ for complex $d\times d$ matrices in fixed orthonormal bases; positive means positive semidefinite. All maps are complex-linear and all dimensions are positive integers. CP means completely positive, coCP means that output transposition composed with the map is CP, and nontrivial means neither. Tensor-stable positivity means positivity at every positive tensor degree. The symbols $\|\cdot\|_\diamond$, $\|\cdot\|_1$ and $\|\cdot\|_\infty$ denote the diamond, trace and spectral norms, respectively; $*$ denotes the Hilbert--Schmidt adjoint. Choi matrices and maximally entangled projections use the normalized, reference-first convention.
--
--   Let $P:M_{d_1}\to M_{d_2}$ be nonzero and $n$-tensor-stable positive, with $n\ge1$. Then
--   $$\frac{d_{\rm CP}(P)}{\|P\|_\diamond}\le\inf_{S\ {\rm separable\ CP}}\|\omega_{d_1}-S(C_P^{\otimes(n-1)})\|_1.$$
--   The maps $S:M_{d_1}^{\otimes(n-1)}\otimes M_{d_2}^{\otimes(n-1)}\to M_{d_1}\otimes M_{d_1}$ may be rescaled and need not preserve trace. $C_P$ is normalized and need not be PSD. The nonzero domain is inherited from Corollary 1; its omission from this printed corollary is documented explicitly.
-- source:
--   Positivity of linear maps under tensor powers, arXiv:1502.05630v2, PDF p. 17, Corollary 3: Choi-state separable-distillation obstruction

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

/-- Corollary 3, PDF p.17: retain the nonzero quotient domain inherited from Corollary 1
(p.15), absent from this printed statement. S is not required to preserve trace. -/
theorem choi_separable_distillation_obstruction [Nonempty A] [Nonempty B]
    (P : MatrixMap A B) (n : ℕ) (hP : NTensorStable P n) (hne : P ≠ 0) :
    distanceCP P / diamond P ≤ sInf (separableErrors P (n-1)) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P37

end
