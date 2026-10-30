-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P45_improvedGapReduction
-- name    : QAlgorithms.Papers.Independent.Extend50.P45.improvedGapReduction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:03:24.719006+00:00
-- url     : https://prove2.me/theorems/88d1e5b0-84f1-4c96-aeac-5bded88bdcdd
-- title:
--   Improved reduction of the positive Hamiltonian gap
-- statement:
--   Let $n$ be the number of qubits. The law $\nu_n$ chooses uniformly one of the $n$ ordered neighboring pairs on the periodic ring and applies an independent Haar $U(4)$ gate. For even $n$, $\nu_n^{\rm bw}$ first applies independent Haar gates on $(1,2),(3,4),\ldots$ and then on $(2,3),(4,5),\ldots,(n,1)$. Each brickwork step has two parallel gate layers. Write $\mu_H$ for normalized Haar measure and
--   $$g(\nu,t)=\left\|\int U^{\otimes t}\otimes\overline U^{\otimes t}\,d\nu(U)-\int U^{\otimes t}\otimes\overline U^{\otimes t}\,d\mu_H(U)\right\|_\infty.$$
--   The norm is the operator norm. Set $L(t)=\lceil2\log_2(4t)+\tfrac32\sqrt{\log_2(4t)}\rceil$ and $F(t)=(\ln t)^5t^{4+3/\sqrt{\log_2t}}$ when $t\ge2$. Define $H_{n,t}=\sum_{i=1}^n(I-P_{i,i+1,t})$, where $P_{i,i+1,t}$ is the Haar moment projection for the indicated two-qubit edge, acting identically on the other wires. Let $\Delta$ denote the least strictly positive eigenvalue, allowing a degenerate zero ground space. For integers $t\ge1$, $n\ge2$ with $n\ge L(t)$,
--   $$\Delta(H_{n,t})\ge\frac{\Delta(H_{L(t),t})}{4L(t)}.$$
--   This reduces the system-size dependence of the spectral-gap bound without changing its moment order.
-- source:
--   Random quantum circuits are approximate unitary $t$-designs in depth $O\left(nt^{5+o(1)}\right)$, arXiv:2203.16571v3, PDF p. 7, Observation 1 (Improved gap reduction), Eq.(17)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P45

noncomputable section

open MeasureTheory

open scoped ComplexConjugate ENNReal

namespace QAlgorithms.Papers.Independent.Extend50.P45

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P45.qubitMatrixMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P45.qubitMatrixBorel

/-- PDF p.7, Observation 1, Eq.(17); Appendix A pp.20–21.
Delta means the least strictly positive eigenvalue, not the gap above one chosen
zero eigenvector. No Lambert-W assertion is imported from the appendix. -/
theorem improvedGapReduction (n t : ℕ) (hn : 2 ≤ n) (ht : 1 ≤ t)
    (hsize : reductionLength t ≤ n) :
    minPositiveEigenvalue (momentHamiltonian (reductionLength t) t) /
      (4 * (reductionLength t : ℝ)) ≤
    minPositiveEigenvalue (momentHamiltonian n t) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P45

end
