-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P45_auxiliaryGap
-- name    : QAlgorithms.Papers.Independent.Extend50.P45.auxiliaryGap
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:06:15.123676+00:00
-- url     : https://prove2.me/theorems/ed48bc74-f836-4484-9bb5-394361f71493
-- title:
--   Unconditional auxiliary-walk moment gap
-- statement:
--   For $n\ge1$, let $\mu_{\rm Cl}$ be uniform sampling of the entire global $n$-qubit Clifford group modulo scalar phase, and let $\mu_{H,1}$ be Haar $U(2)$ on the first qubit. Set $\sigma=\mu_{\rm Cl}*\mu_{H,1}*\mu_{\rm Cl}$, with independent factors. Scalar phases of Clifford representatives are absorbed by the single-qubit Haar law.
--
--   With $g$ the operator-norm distance from the normalized Haar $t$-moment, every integer $n\ge1$ and $t\ge1$ satisfies
--   $$g(\sigma,t)\le1-\frac{3}{2(2^{2n}-1)}.$$
--   This controls all moments of the auxiliary walk without a restriction connecting $n$ and $t$. The finite enumeration in Lean ranges over the complete projective Clifford group.
-- source:
--   Random quantum circuits are approximate unitary $t$-designs in depth $O\left(nt^{5+o(1)}\right)$, arXiv:2203.16571v3, PDF p. 10, Lemma 3: unconditional gap of the auxiliary walk, Eq.(27)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P45

noncomputable section

open MeasureTheory

open scoped ComplexConjugate ENNReal

namespace QAlgorithms.Papers.Independent.Extend50.P45

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P45.qubitMatrixMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Extend50.P45.qubitMatrixBorel

/-- PDF p.10, Lemma 3, Eq.(27), with auxiliary law from p.9 Eq.(26).
The finite-type instance enumerates the entire frozen projective Clifford group. -/
theorem auxiliaryGap (n t : ℕ) [Fintype (Clifford.ProjectiveGroup n)]
    (hn : 1 ≤ n) (ht : 1 ≤ t) :
    momentDistance (auxiliaryLaw n) t ≤
      1 - (3 / 2 : ℝ) / ((2 : ℝ) ^ (2 * n) - 1) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P45

end
