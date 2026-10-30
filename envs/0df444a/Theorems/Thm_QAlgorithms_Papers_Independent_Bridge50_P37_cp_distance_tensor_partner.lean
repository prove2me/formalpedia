-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P37_cp_distance_tensor_partner
-- name    : QAlgorithms.Papers.Independent.Bridge50.P37.cp_distance_tensor_partner
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:50:59.210581+00:00
-- url     : https://prove2.me/theorems/6ae7e1d6-7784-43f0-8ae7-0c39884a0cbc
-- title:
--   Lemma 6: distance to CP bounded by a positive tensor partner
-- statement:
--   Write $M_d$ for complex $d\times d$ matrices in fixed orthonormal bases; positive means positive semidefinite. All maps are complex-linear and all dimensions are positive integers. CP means completely positive, coCP means that output transposition composed with the map is CP, and nontrivial means neither. Tensor-stable positivity means positivity at every positive tensor degree. The symbols $\|\cdot\|_\diamond$, $\|\cdot\|_1$ and $\|\cdot\|_\infty$ denote the diamond, trace and spectral norms, respectively; $*$ denotes the Hilbert--Schmidt adjoint. Choi matrices and maximally entangled projections use the normalized, reference-first convention.
--
--   Let $P:M_{d_1}\to M_{d_2}$ be positive and $R:M_{d_1}\to M_{d_1}$ any complex-linear map for which $R\otimes P$ is positive. With normalized $C_P=(\mathrm{id}_{d_1}\otimes P)(\omega_{d_1})$ and $d_{\rm CP}(P)=(\|C_P\|_1-\operatorname{tr}C_P)/2$,
--   $$d_{\rm CP}(P)\le\|\mathrm{id}_{d_1}-R\|_\diamond\|P\|_\diamond.$$
--   The bound holds for every such actual tensor partner. No separate positivity, CP, trace preservation or contraction condition is placed on $R$.
-- source:
--   Positivity of linear maps under tensor powers, arXiv:1502.05630v2, PDF p. 14, Lemma 6: distance to CP bounded by a positive tensor partner

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

/-- Lemma 6, PDF pp.14--15: R is arbitrary complex-linear; only R tensor P is assumed positive. -/
theorem cp_distance_tensor_partner [Nonempty A] [Nonempty B] (P : MatrixMap A B)
    (hP : IsPositiveMap P) (R : MatrixMap A A) (hR : IsPositiveMap (tensorLinearMap R P)) :
    distanceCP P ≤ diamond ((LinearMap.id : MatrixMap A A) - R) * diamond P := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P37

end
