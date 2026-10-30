-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P37_recurrence_protocol_bound
-- name    : QAlgorithms.Papers.Independent.Bridge50.P37.recurrence_protocol_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:57:44.296897+00:00
-- url     : https://prove2.me/theorems/7a0f6e88-4c86-4e77-8624-76f634922fb9
-- title:
--   Theorem 8: recurrence bound, normalized reading established by the proof
-- statement:
--   Write $M_d$ for complex $d\times d$ matrices in fixed orthonormal bases; positive means positive semidefinite. All maps are complex-linear and all dimensions are positive integers. CP means completely positive, coCP means that output transposition composed with the map is CP, and nontrivial means neither. Tensor-stable positivity means positivity at every positive tensor degree. The symbols $\|\cdot\|_\diamond$, $\|\cdot\|_1$ and $\|\cdot\|_\infty$ denote the diamond, trace and spectral norms, respectively; $*$ denotes the Hilbert--Schmidt adjoint. Choi matrices and maximally entangled projections use the normalized, reference-first convention.
--
--   Let $P:M_{d_1}\to M_{d_2}$ be positive, with $d_1\ge2$ and $P\circ\Gamma_{d_1}$ not CP. Put $B=I_{d_1}\otimes P(I_{d_1})$ and $p=\lambda_{\max}(B^{-1/2}C_PB^{-1/2})$, using the generalized inverse with zero on $\ker B$. Then $1/d_1<p\le1$. If $P$ is $n$-tensor-stable positive with $n\ge2$,
--   $$\frac{d_{\rm CP}(P)}{\|P\|_\diamond}\le2(1-p)\,g_{d_1}(p)^{\lfloor\log_2(n-1)\rfloor},\qquad g_d(q)=\frac{(d-1)(d(1+q)+2)}{q^2d^3-2qd+d^2+d-1}.$$
--   For $1/d<q\le1$, $0\le g_d(q)<1$, including the removable endpoint $g_d(1)=2/(d+1)$. This follows the proof's normalized conclusion: printed Eq. (23) omits $\|P\|_\diamond$, and the last proof display mistakenly writes $T$ in its numerator. Positive scaling rules out the unnormalized reading. Independent moderation of this correction is pending.
-- source:
--   Positivity of linear maps under tensor powers, arXiv:1502.05630v2, PDF p. 21, Theorem 8: recurrence bound, normalized reading established by the proof

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

/-- Theorem 8, PDF pp.20--21, CORRECTED from the final proof display and Corollary 3:
printed Eq. (23) omits division by ||P||diamond, and the last proof display calls P 'T'.
Positive rescaling disproves the unnormalized reading. n>=2 comes from n-1 copies;
g is canceled at p=1, giving 2/(d+1). Independent moderation is required. -/
theorem recurrence_protocol_bound (d1 d2 n : ℕ) [NeZero d1] [NeZero d2]
    (hd : 2 ≤ d1) (hn : 2 ≤ n) (P : MatrixMap (Fin d1) (Fin d2))
    (hP : IsPositiveMap P) (hncp : ¬ Entanglement.IsCompletelyPositive (P.comp (reductionMap (Fin d1))))
    (hstable : NTensorStable P n) :
    let p := recurrenceParameter P
    (1 : ℝ)/d1 < p ∧ p ≤ 1 ∧
    distanceCP P / diamond P ≤ 2*(1-p) * recurrenceG d1 p ^ (Nat.log 2 (n-1)) ∧
    (∀ q : ℝ, (1 : ℝ)/d1 < q → q ≤ 1 → 0 ≤ recurrenceG d1 q ∧ recurrenceG d1 q < 1) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P37

end
