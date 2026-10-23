-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P40_traceOperatorFactorTwo
-- name    : QAlgorithms.Papers.Independent.Gap48.P40.traceOperatorFactorTwo
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T05:18:20.673976+00:00
-- url     : https://prove2.me/theorems/6644a29f-de8b-4149-b377-5387bc37f964
-- title:
--   §IV, Lemma 4: traceless trace/operator norm factor two
-- statement:
--   Let $N$ be any genuine unitarily invariant norm on $d\times d$ complex matrices. Write $E=\operatorname{diag}(1,0,\ldots)$ and, when $d\ge2$, $F=\operatorname{diag}(1,-1,0,\ldots)$. The symbols $\|\cdot\|_\infty$, $\|\cdot\|_1$ and $\|\cdot\|_2$ mean operator, full trace and Hilbert–Schmidt norms, respectively. For every traceless Hermitian matrix $A$ in positive dimension,
--
--   $$
--   \|A\|_1\ge2\|A\|_\infty.
--   $$
--
--   This explains the factor two in normalized trace distance.
-- source:
--   Continuity bounds on the quantum relative entropy, arXiv:quant-ph/0503218v3, PDF p. 3, §IV, Lemma 4: traceless trace/operator norm factor two

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

/-- PDF pp.3–4, Lemma 4: traceless Hermitian matrices have the factor two. -/
theorem traceOperatorFactorTwo {d : ℕ} (hd : 0 < d) (A : Mat d)
    (hA : A.IsHermitian) (htrace : A.trace = 0) :
    2 * specNorm A ≤ traceNorm A := by sorry

end QAlgorithms.Papers.Independent.Gap48.P40

end
