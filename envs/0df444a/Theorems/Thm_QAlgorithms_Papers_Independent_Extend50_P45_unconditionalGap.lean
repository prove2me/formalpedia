-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P45_unconditionalGap
-- name    : QAlgorithms.Papers.Independent.Extend50.P45.unconditionalGap
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:04:04.628279+00:00
-- url     : https://prove2.me/theorems/9f409fd7-da89-4a3f-b491-041f8be2fc98
-- title:
--   Unconditional local Haar moment gap
-- statement:
--   Let $n$ be the number of qubits. The law $\nu_n$ chooses uniformly one of the $n$ ordered neighboring pairs on the periodic ring and applies an independent Haar $U(4)$ gate. For even $n$, $\nu_n^{\rm bw}$ first applies independent Haar gates on $(1,2),(3,4),\ldots$ and then on $(2,3),(4,5),\ldots,(n,1)$. Each brickwork step has two parallel gate layers. Write $\mu_H$ for normalized Haar measure and
--   $$g(\nu,t)=\left\|\int U^{\otimes t}\otimes\overline U^{\otimes t}\,d\nu(U)-\int U^{\otimes t}\otimes\overline U^{\otimes t}\,d\mu_H(U)\right\|_\infty.$$
--   The norm is the operator norm. Set $L(t)=\lceil2\log_2(4t)+\tfrac32\sqrt{\log_2(4t)}\rceil$ and $F(t)=(\ln t)^5t^{4+3/\sqrt{\log_2t}}$ when $t\ge2$. For all integers $n\ge2$ and $t\ge1$,
--   $$g(\nu_n,t)\le1-\frac{1}{120000\,n^5\,2^{2n}}.$$
--   No parity or $n\ge L(t)$ restriction is required. The bound is uniform in the moment order.
-- source:
--   Random quantum circuits are approximate unitary $t$-designs in depth $O\left(nt^{5+o(1)}\right)$, arXiv:2203.16571v3, PDF p. 7, Theorem 1 (Unconditional gap), Eq.(18)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P45

noncomputable section

open MeasureTheory

open scoped ComplexConjugate ENNReal

namespace QAlgorithms.Papers.Independent.Extend50.P45

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P45.qubitMatrixMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P45.qubitMatrixBorel

/-- PDF p.7, Theorem 1, Eq.(18): all n >= 2, including odd n, and every t >= 1.
The auxiliary Clifford estimates are conclusions elsewhere, never hypotheses here. -/
theorem unconditionalGap (n t : ℕ) (hn : 2 ≤ n) (ht : 1 ≤ t) :
    momentDistance (localHaarRingLaw n) t ≤
      1 - ((120000 : ℝ) * (n : ℝ) ^ 5 * (2 : ℝ) ^ (2 * n))⁻¹ := by sorry

end QAlgorithms.Papers.Independent.Extend50.P45

end
