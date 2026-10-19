-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P50_lemma_5_12
-- name    : QAlgorithms.Papers.Independent.Information100.P50.lemma_5_12
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:07:28.613882+00:00
-- url     : https://prove2.me/theorems/c5a59f36-9309-4667-8360-ad8ae3dbb16e
-- title:
--   Lemma 5.12: For bounded endpoint operator-convex f with f(1)=0, h(t)=f(0+)+f'(infinity)t-f(t) is nonnegative operator mono
-- statement:
--   All spaces are finite-dimensional complex Euclidean spaces. Input and output dimensions are positive wherever states or extreme eigenvalues occur. The Choi matrix $J$ is unnormalized and has output factor first. Write $\|\Theta\|_\diamond$ for the full completely bounded trace norm, $\|A\|_\infty$ for the operator norm, and $\Theta^*$ for the Hilbert–Schmidt adjoint.
--
--   Let $f:(0,\infty)\to\mathbb R$ be operator convex in every matrix size, with $f(1)=0$ and finite real limits $a=f(0+)$ and $b=\lim_{t\to\infty}f(t)/t$. The maximal divergence $\widehat D_f$ is defined independently by the regularized state perspective and a supremum over a common bipartite density input. Outputs are not required to have trace one.
--
--   Set $h(t)=a+bt-f(t)$ for $t>0$. Then $h$ is nonnegative and operator monotone in every matrix size, with $h(0+)=0$ and $\lim_{t\to\infty}h(t)/t=0$. There is a Kubo–Ando connection $\sigma_h$ with representing function $h$, and for all PSD matrices $A,B$,
--
--   $$\widehat D_f(A\|B)=a\operatorname{tr}B+b\operatorname{tr}A-\operatorname{tr}(B\sigma_h A).$$
--
--   This is a connection rather than necessarily a normalized mean; the zero connection is permitted. The decomposition separates the affine part of a bounded maximal divergence.
-- source:
--   Quantitative upper bounds for certain quantum channel divergences, arXiv:2610.16270v1, PDF p. 21, Lemma 5.12

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P50

noncomputable section

open scoped Matrix ComplexConjugate ENNReal Topology ComplexOrder Kronecker

open Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P50

/-- Lemma 5.12, source PDF p.21. The remainder yields a connection, possibly zero;
normalization or h(1)>0 would exclude affine generators and is deliberately absent. -/
theorem lemma_5_12 (f : BoundedGenerator) :
    (∀ t > 0, 0 ≤ affineRemainder f.f t) ∧ OperatorMonotone (affineRemainder f.f) ∧
    Tendsto (affineRemainder f.f) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
    Tendsto (fun t : ℝ => affineRemainder f.f t / t) atTop (𝓝 0) ∧
    ∃ s : Connection, s.f = affineRemainder f.f ∧
      ∀ (n : ℕ) (A B : M n), A.PosSemidef → B.PosSemidef →
        stateDivergence f.f A B = atZero f.f * B.trace.re + atInfinity f.f * A.trace.re -
          (connectionOp s B A).trace.re := by sorry

end QAlgorithms.Papers.Independent.Information100.P50

end
