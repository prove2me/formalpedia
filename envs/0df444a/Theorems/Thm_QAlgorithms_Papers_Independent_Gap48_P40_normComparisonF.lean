-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P40_normComparisonF
-- name    : QAlgorithms.Papers.Independent.Gap48.P40.normComparisonF
-- status  : Disproved
-- author  : @Goku
-- created : 2026-10-22T05:17:30.206995+00:00
-- url     : https://prove2.me/theorems/d5dee2f3-8077-46fa-be95-6abf5bb09711
-- title:
--   §IV, Lemma 3: traceless Hermitian rescaled norm comparison
-- statement:
--   Let $N$ be any genuine unitarily invariant norm on $d\times d$ complex matrices. Write $E=\operatorname{diag}(1,0,\ldots)$ and, when $d\ge2$, $F=\operatorname{diag}(1,-1,0,\ldots)$. The symbols $\|\cdot\|_\infty$, $\|\cdot\|_1$ and $\|\cdot\|_2$ mean operator, full trace and Hilbert–Schmidt norms, respectively. If $d\ge2$, $A=A^*$ and $\operatorname{Tr}A=0$, then
--
--   $$
--   \frac{\|A\|_\infty}{\|F\|_\infty}\le\frac{N(A)}{N(F)}\le\frac{\|A\|_1}{\|F\|_1}.
--   $$
--
--   For every prescribed $a\ge0$, the matrix $B=(a/N(F))F$ has $N(B)=a$ and equality in both comparisons.
--
--   This gives the stronger normalization appropriate to differences of states.
-- source:
--   Continuity bounds on the quantum relative entropy, arXiv:quant-ph/0503218v3, PDF p. 3, §IV, Lemma 3: traceless Hermitian rescaled norm comparison

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

/-- PDF p.3, Lemma 3 and its following equality sentence. -/
theorem normComparisonF {d : ℕ} (hd : 2 ≤ d) (N : Mat d → ℝ)
    (hN : IsUINorm N) (A : Mat d) (hA : A.IsHermitian) (htrace : A.trace = 0) :
    (specNorm A / specNorm (matrixF d) ≤ rescaled N A ∧
      rescaled N A ≤ traceNorm A / traceNorm (matrixF d)) ∧
    (∀ a : ℝ, 0 ≤ a →
      let B := ((a / N (matrixF d) : ℝ) : ℂ) • matrixF d
      N B = a ∧ specNorm B / specNorm (matrixF d) = rescaled N B ∧
        rescaled N B = traceNorm B / traceNorm (matrixF d)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P40

end
