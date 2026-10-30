-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P37_parallel_finite_error
-- name    : QAlgorithms.Papers.Independent.Bridge50.P37.parallel_finite_error
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:50:19.573002+00:00
-- url     : https://prove2.me/theorems/fa0d92d5-13c5-4153-a2f1-102d7a63e78a
-- title:
--   Lemma 5: finite-use unassisted error bound for tensor-stable maps
-- statement:
--   Write $M_d$ for complex $d\times d$ matrices in fixed orthonormal bases; positive means positive semidefinite. All maps are complex-linear and all dimensions are positive integers. CP means completely positive, coCP means that output transposition composed with the map is CP, and nontrivial means neither. Tensor-stable positivity means positivity at every positive tensor degree. The symbols $\|\cdot\|_\diamond$, $\|\cdot\|_1$ and $\|\cdot\|_\infty$ denote the diamond, trace and spectral norms, respectively; $*$ denotes the Hilbert--Schmidt adjoint. Choi matrices and maximally entangled projections use the normalized, reference-first convention.
--
--   Under Theorem 6's hypotheses and for positive integers $n,m$, let $\mathcal E:M_{d_2}^{\otimes n}\to M_{d_1}^{\otimes m}$ and $\mathcal D:M_{d_2}^{\otimes m}\to M_{d_2}^{\otimes n}$ range over all CPTP maps. Then
--   $$\inf_{\mathcal E,\mathcal D}\frac12\|\mathrm{id}_{d_2}^{\otimes n}-\mathcal D\circ T^{\otimes m}\circ\mathcal E\|_\diamond\ge1-d_2^{-2n}-\frac{(\|P^*(I_{d_2})\|_\infty\|R\circ T\|_\diamond)^m+2}{\|(P^*\otimes\mathrm{id}_{d_2})(\omega_{d_2})\|_1^n}.$$
--   The infimum is over actual encoders and decoders and has a nonempty bounded error set. The $d_2^{-2n}$ term is separate, and the whole norm product is raised to $m$.
-- source:
--   Positivity of linear maps under tensor powers, arXiv:1502.05630v2, PDF p. 13, Lemma 5: finite-use unassisted error bound for tensor-stable maps

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

/-- Lemma 5, PDF pp.13--14: the d2^(-2n) term is separately subtracted; the ENTIRE
product of norms is raised to m, then 2 is added. Infimum over actual CPTP codes. -/
theorem parallel_finite_error [Nonempty A] [Nonempty B] [Nonempty C]
    (T : MatrixMap A B) (P : MatrixMap C B) (R : MatrixMap B C) (hT : IsChannel T)
    (hP : TensorStable P) (hs : Function.Surjective P) (hu : P 1 = 1)
    (hncp : ¬ Entanglement.IsCompletelyPositive P) (hR : P.comp R = LinearMap.id)
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    sInf (parallelErrors (L := Fin n → B) T m) ≥
      1 - 1 / (Fintype.card B : ℝ)^(2*n) -
        ((specNorm (hsAdjoint P 1) * diamond (R.comp T))^m + 2) /
          traceNorm (tensorLinearMap (hsAdjoint P) (LinearMap.id : MatrixMap B B) (normalizedEntangledProjection B))^n := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P37

end
