-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P21_holevo_diagonal_qubit
-- name    : QAlgorithms.Papers.Independent.Advance50.P21.holevo_diagonal_qubit
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:05:02.991838+00:00
-- url     : https://prove2.me/theorems/e89b5c9d-08c6-4209-bcd0-fc131b208827
-- title:
--   Unnumbered qubit fixed-diagonal-port Holevo bound (7.12)
-- statement:
--   For $a,\delta\in[0,1]$, fix the qubit port $\sigma=\delta|0\rangle\langle0|+(1-\delta)|1\rangle\langle1|$. Let $\mathcal E_{a,\sigma}(X)=\operatorname{Tr}_2(U_a(X\otimes\sigma)U_a^\dagger)$ with $U_a=\sqrt a\,I+i\sqrt{1-a}\,S$ and swap $S$. Write $\chi$ for its single-use Holevo quantity over all finite normalized input ensembles, measured in nats. With $h(\delta)=-\delta\log\delta-(1-\delta)\log(1-\delta)$, interpreted continuously at the endpoints,
--   $$\chi(\mathcal E_{a,\sigma})\le\log2-(1-a)h(\delta).$$
--   This retains the explicit diagonal-qubit specialization of the general bound.
-- source:
--   Entropy power inequalities for qudits, arXiv:1503.04213v3, PDF p. 27, Unnumbered qubit fixed-diagonal-port Holevo bound (7.12)

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

/-- PDF pp.26–27, (7.12): fixed diagonal qubit port, binary entropy in nats. -/
theorem holevo_diagonal_qubit (delta : ℝ) (hdelta : delta ∈ Set.Icc (0 : ℝ) 1)
    (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    holevoNats (fixedPort a (diagonalPort delta)) ≤
      Real.log 2 - (1 - a) * Real.binEntropy delta := by sorry

end QAlgorithms.Papers.Independent.Advance50.P21

end
