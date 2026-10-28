-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P40_normComparisonE
-- name    : QAlgorithms.Papers.Independent.Gap48.P40.normComparisonE
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T05:16:49.661935+00:00
-- url     : https://prove2.me/theorems/0d5cac07-1b64-4cab-b936-2d7eee9f67b2
-- title:
--   §IV, Lemma 2: norm comparison normalized by E
-- statement:
--   Let $N$ be any genuine unitarily invariant norm on $d\times d$ complex matrices. Write $E=\operatorname{diag}(1,0,\ldots)$ and, when $d\ge2$, $F=\operatorname{diag}(1,-1,0,\ldots)$. The symbols $\|\cdot\|_\infty$, $\|\cdot\|_1$ and $\|\cdot\|_2$ mean operator, full trace and Hilbert–Schmidt norms, respectively. For $d>0$ and every matrix $A$,
--
--   $$
--   \|A\|_\infty\le\frac{N(A)}{N(E)}\le\|A\|_1.
--   $$
--
--   This compares every UI norm after fixing its rank-one normalization.
-- source:
--   Continuity bounds on the quantum relative entropy, arXiv:quant-ph/0503218v3, PDF p. 3, §IV, Lemma 2: norm comparison normalized by E

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

/-- PDF p.3, Lemma 2: norm comparison normalized by E. -/
theorem normComparisonE {d : ℕ} (hd : 0 < d) (N : Mat d → ℝ)
    (hN : IsUINorm N) (A : Mat d) :
    specNorm A ≤ N A / N (matrixE d) ∧ N A / N (matrixE d) ≤ traceNorm A := by sorry

end QAlgorithms.Papers.Independent.Gap48.P40

end
