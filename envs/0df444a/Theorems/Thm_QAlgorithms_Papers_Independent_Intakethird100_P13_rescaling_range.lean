-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P13_rescaling_range
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P13.rescaling_range
-- status  : Proved
-- author  : @Gohan
-- created : 2026-11-01T04:58:21.50235+00:00
-- url     : https://prove2.me/theorems/bf1a8ade-0303-4c86-90ef-a33d9d4f7d7b
-- title:
--   Range of the regular rescaling quotient
-- statement:
--   Let $\gamma,s\in[0,1]$ and assume $1-\gamma s>0$, the domain of the displayed real quotient. Then
--
--   $$0\le\frac{1-\gamma}{1-\gamma s}\le1.$$
--
--   In the decomposition proof $s=S_{30}\ge0$. The singular pair $(1,1)$ is handled by the physical endpoint characterization and is not assigned a quotient value.
-- source:
--   Simulation of non-Pauli Channels, arXiv:1706.05384v2, PDF p. 12, Lemma 20

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P13

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Intakethird100.P13

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arXiv:1706.05384v2 PDF p.12, Lemma 20.
Domain correction: the printed proof uses a quotient at the singular pair (1,1);
strict positivity states its ordinary real-quotient domain. -/
theorem rescaling_range (gamma s30 : ℝ) (hg0 : 0 ≤ gamma) (hg1 : gamma ≤ 1)
    (hs0 : 0 ≤ s30) (hs1 : s30 ≤ 1) (hden : 0 < 1-gamma*s30) :
    rescaling gamma s30 ∈ Set.Icc (0 : ℝ) 1 := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P13

end
