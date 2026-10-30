-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P45_tensorProductExpanders
-- name    : QAlgorithms.Papers.Independent.Extend50.P45.tensorProductExpanders
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:04:53.254665+00:00
-- url     : https://prove2.me/theorems/1ce893b8-b43d-4766-b5ee-4200e2dbac57
-- title:
--   Quantitative tensor-product expander bounds
-- statement:
--   Let $n$ be the number of qubits. The law $\nu_n$ chooses uniformly one of the $n$ ordered neighboring pairs on the periodic ring and applies an independent Haar $U(4)$ gate. For even $n$, $\nu_n^{\rm bw}$ first applies independent Haar gates on $(1,2),(3,4),\ldots$ and then on $(2,3),(4,5),\ldots,(n,1)$. Each brickwork step has two parallel gate layers. Write $\mu_H$ for normalized Haar measure and
--   $$g(\nu,t)=\left\|\int U^{\otimes t}\otimes\overline U^{\otimes t}\,d\nu(U)-\int U^{\otimes t}\otimes\overline U^{\otimes t}\,d\mu_H(U)\right\|_\infty.$$
--   The norm is the operator norm. Set $L(t)=\lceil2\log_2(4t)+\tfrac32\sqrt{\log_2(4t)}\rceil$ and $F(t)=(\ln t)^5t^{4+3/\sqrt{\log_2t}}$ when $t\ge2$. For all integers $t\ge2$ and $n\ge2$ with $n\ge L(t)$,
--   $$g(\nu_n,t)\le1-\frac1{10^{13}nF(t)}.$$
--   For the same range with even $n$, also
--   $$g(\nu_n^{\rm bw},t)\le1-\frac1{3\cdot10^{13}F(t)}.$$
--   Both numerical constants are absolute; the brickwork denominator has no system-size factor. These estimates control moment convergence for the two architectures.
-- source:
--   Random quantum circuits are approximate unitary $t$-designs in depth $O\left(nt^{5+o(1)}\right)$, arXiv:2203.16571v3, PDF p. 7, Theorem 2 (Tensor product expanders)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P45

noncomputable section

open MeasureTheory

open scoped ComplexConjugate ENNReal

namespace QAlgorithms.Papers.Independent.Extend50.P45

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P45.qubitMatrixMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P45.qubitMatrixBorel

/-- PDF p.7, Theorem 2: both architectures with C=10^13, on the natural
logarithmic domain t >= 2. Only the brickwork clause requires even n. -/
theorem tensorProductExpanders (n t : ℕ) (hn : 2 ≤ n) (ht : 2 ≤ t)
    (hsize : reductionLength t ≤ n) :
    momentDistance (localHaarRingLaw n) t ≤
      1 - ((10 : ℝ) ^ 13 * n * designFactor t)⁻¹ ∧
    (Even n → momentDistance (brickworkLaw n) t ≤
      1 - (3 * (10 : ℝ) ^ 13 * designFactor t)⁻¹) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P45

end
