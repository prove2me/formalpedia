-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P37_unital_tensor_norm_characterization
-- name    : QAlgorithms.Papers.Independent.Bridge50.P37.unital_tensor_norm_characterization
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:58:27.090916+00:00
-- url     : https://prove2.me/theorems/b10a11a8-14cc-40e8-b4c7-555e2ef2dc3a
-- title:
--   Unnumbered concluding norm characterization of tensor-stable positivity
-- statement:
--   Write $M_d$ for complex $d\times d$ matrices in fixed orthonormal bases; positive means positive semidefinite. All maps are complex-linear and all dimensions are positive integers. The symbols $\|\cdot\|_\diamond$, $\|\cdot\|_1$ and $\|\cdot\|_\infty$ denote the diamond, trace and spectral norms, respectively; $*$ denotes the Hilbert--Schmidt adjoint. Choi matrices and maximally entangled projections use the normalized, reference-first convention.
--
--   Let $T:M_{d_1}\to M_{d_2}$ be positive and unital, and let $n\ge1$. Then
--   $$T^{\otimes n}\text{ is positive}\quad\Longleftrightarrow\quad\|T^{\otimes n}\|_{\infty\to\infty}=1.$$
--   The induced norm uses the spectral matrix norm on all operators. Positive dimensions make the identity nonzero. The source attributes this characterization to Paulsen [24].
-- source:
--   Positivity of linear maps under tensor powers, arXiv:1502.05630v2, PDF p. 22, Unnumbered concluding norm characterization of tensor-stable positivity

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

/-- Explicit norm characterization concluding PDF p.22, attributed to Paulsen [24]. -/
theorem unital_tensor_norm_characterization [Nonempty A] [Nonempty B]
    (T : MatrixMap A B) (hT : IsPositiveMap T) (hu : T 1 = 1) (n : ℕ) (hn : 0 < n) :
    NTensorStable T n ↔ inducedInfinity (tensorLinearPower T n) = 1 := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P37

end
