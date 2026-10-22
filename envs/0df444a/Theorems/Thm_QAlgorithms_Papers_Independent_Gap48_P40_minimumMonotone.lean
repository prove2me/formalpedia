-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P40_minimumMonotone
-- name    : QAlgorithms.Papers.Independent.Gap48.P40.minimumMonotone
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:23:48.22299+00:00
-- url     : https://prove2.me/theorems/8275649a-32b9-4401-98b9-02ae73ea2d3e
-- title:
--   §VI, Lemma 7: monotonicity of the minimum relative entropy
-- statement:
--   All matrices act on a complex Hilbert space of positive finite dimension $d$. A state is positive semidefinite with trace one. All logarithms are natural, and $D(\rho\|\sigma)$ denotes support-aware Umegaki relative entropy, with value $+\infty$ when support containment fails. Let $N$ be any genuine unitarily invariant norm on $d\times d$ complex matrices. Write $E=\operatorname{diag}(1,0,\ldots)$ and, when $d\ge2$, $F=\operatorname{diag}(1,-1,0,\ldots)$. The symbols $\|\cdot\|_\infty$, $\|\cdot\|_1$ and $\|\cdot\|_2$ mean operator, full trace and Hilbert–Schmidt norms, respectively. Let $d\ge2$ and define $m_N(T)$ as the extended infimum of $D(\rho\|\sigma)$ over pairs of states satisfying $N(\rho-\sigma)=T$. If $0\le T_1\le T_2\le N(F)$, then
--
--   $$
--   m_N(T_1)\le m_N(T_2).
--   $$
--
--   The minimum relative entropy is monotone on the physical interval of raw norm distances.
--
--   At the endpoints, $m_N(0)=0$ and $m_N(N(F))=+∞$.
-- source:
--   Continuity bounds on the quantum relative entropy, arXiv:quant-ph/0503218v3, PDF p. 6, §VI, Lemma 7: monotonicity of the minimum relative entropy

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P40

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology Matrix.Norms.L2Operator

open Filter MeasureTheory Asymptotics

open QAlgorithms

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P50 (IsUINorm)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P60 (copies)

open QAlgorithms.Papers.Independent.Information100.P44 (Mat)

namespace QAlgorithms.Papers.Independent.Gap48.P40

/-- PDF p.6, Lemma 7: monotonicity on the physical raw-distance interval. -/
theorem minimumMonotone {d : ℕ} (hd : 2 ≤ d) (N : Mat d → ℝ) (hN : IsUINorm N)
    (T1 T2 : ℝ) (hT1 : 0 ≤ T1) (horder : T1 ≤ T2) (hT2 : T2 ≤ N (matrixF d)) :
    minimumAt d N T1 ≤ minimumAt d N T2 ∧
    minimumAt d N 0 = 0 ∧ minimumAt d N (N (matrixF d)) = ⊤ := by sorry

end QAlgorithms.Papers.Independent.Gap48.P40

end
