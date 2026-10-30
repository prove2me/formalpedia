-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P21_partialSwap_kraus
-- name    : QAlgorithms.Papers.Independent.Advance50.P21.partialSwap_kraus
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T21:53:41.309987+00:00
-- url     : https://prove2.me/theorems/70a3eda0-0900-45e7-adff-18e877858d41
-- title:
--   Unnumbered CPTP/Kraus realization (4.7), (4.9), (4.15), and §4.4
-- statement:
--   Let $d\ge1$, $a\in[0,1]$, $S|i,j\rangle=|j,i\rangle$, and $U_a=\sqrt a\,I+i\sqrt{1-a}\,S$. The matrix $U_a$ is unitary. Define $\mathcal E_a(X)=\operatorname{Tr}_2(U_aXU_a^\dagger)$ and
--   $$A_k=\sqrt a\,(I\otimes\langle k|)+i\sqrt{1-a}\,(\langle k|\otimes I),\qquad k=1,\ldots,d.$$
--   Then
--   $$\sum_k A_k^\dagger A_k=I,\qquad\mathcal E_a(X)=\sum_k A_kXA_k^\dagger$$
--   for every joint operator $X$. Consequently $\mathcal E_a$ is completely positive and trace preserving, including on entangled inputs. This is the full $d$-Kraus realization, separate from the product-state formula.
-- source:
--   Entropy power inequalities for qudits, arXiv:1503.04213v3, PDF p. 10, Unnumbered CPTP/Kraus realization (4.7), (4.9), (4.15), and §4.4

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P21

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P21

open scoped BigOperators Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P26 (Mat)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P76 (swapMatrix)

open QAlgorithms.Papers.Independent.Dependency50.P16 (simplex orderedSpectrum majorizedBy)

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble)

open QAlgorithms.Papers.Independent.Information100.P49 (thermalEntropy)

open QAlgorithms.Papers.Independent.Claimed50.P11 (thermalEntropyInverse)

/-- PDF pp.9–11, (4.7),(4.9),(4.15): unitary realization and d normalized Kraus operators.
The operator equality holds on arbitrary joint operators, including entangled states. -/
theorem partialSwap_kraus {d : ℕ} (hd : 0 < d) (a : ℝ)
    (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    partialSwapUnitary d a ∈ Matrix.unitaryGroup (Fin d × Fin d) ℂ ∧
    IsKrausFamily (partialSwapKraus d a) ∧
    IsChannel (partialSwapChannel d a) ∧
    (∀ X, partialSwapChannel d a X = krausApply (partialSwapKraus d a) X) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P21

end
