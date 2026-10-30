-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P37_tensor_stable_parallel_strong_converse
-- name    : QAlgorithms.Papers.Independent.Bridge50.P37.tensor_stable_parallel_strong_converse
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:49:29.750519+00:00
-- url     : https://prove2.me/theorems/922a3b1a-c2ce-4536-9a7b-0b22cb6e8077
-- title:
--   Equation (14): unassisted strong converse rate from tensor-stable positivity
-- statement:
--   Write $M_d$ for complex $d\times d$ matrices in fixed orthonormal bases; positive means positive semidefinite. All maps are complex-linear and all dimensions are positive integers. The symbols $\|\cdot\|_\diamond$, $\|\cdot\|_1$ and $\|\cdot\|_\infty$ denote the diamond, trace and spectral norms, respectively; $*$ denotes the Hilbert--Schmidt adjoint. Choi matrices and maximally entangled projections use the normalized, reference-first convention.
--
--   Under Theorem 6's channel, map and right-inverse hypotheses, set $a=\|R\circ T\|_\diamond\|P^*(I_{d_2})\|_\infty$ and $k=\|(P^*\otimes\mathrm{id}_{d_2})(\omega_{d_2})\|_1$. Then
--   $$b_{\rm sc}=\frac{\log_2(a)\log_2d_2}{\log_2k}$$
--   is a strong-converse rate for actual unassisted parallel codes. If $m_\nu\to\infty$ and $\liminf_\nu n_\nu\log_2(d_2)/m_\nu>b_{\rm sc}$, the actual half-diamond errors tend exponentially to one. Moreover,
--   $$B(T,P,R)\le b_{\rm sc},\qquad k\le\|P^*\|_\diamond,$$
--   where $B(T,P,R)$ is Theorem 6's bound. The Choi projection is normalized, and $k>1$ follows from the stated map hypotheses.
-- source:
--   Positivity of linear maps under tensor powers, arXiv:1502.05630v2, PDF p. 13, Equation (14): unassisted strong converse rate from tensor-stable positivity

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

/-- Eq. (14), PDF pp.13--14: unassisted strong converse and its comparison with Theorem 6.
The denominator is the normalized Choi TRACE norm, not the adjoint diamond norm. -/
theorem tensor_stable_parallel_strong_converse [Nonempty A] [Nonempty B] [Nonempty C]
    (T : MatrixMap A B) (P : MatrixMap C B) (R : MatrixMap B C) (hT : IsChannel T)
    (hP : TensorStable P) (hs : Function.Surjective P) (hu : P 1 = 1)
    (hncp : ¬ Entanglement.IsCompletelyPositive P) (hR : P.comp R = LinearMap.id) :
    ParallelStrongConverse T (converseBound T P R) ∧
    capacityBound T P R ≤ converseBound T P R ∧
    traceNorm (tensorLinearMap (hsAdjoint P) (LinearMap.id : MatrixMap B B) (normalizedEntangledProjection B)) ≤
      diamond (hsAdjoint P) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P37

end
