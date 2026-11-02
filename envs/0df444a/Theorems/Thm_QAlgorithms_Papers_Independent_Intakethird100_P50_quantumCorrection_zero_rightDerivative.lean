-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P50_quantumCorrection_zero_rightDerivative
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P50.quantumCorrection_zero_rightDerivative
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:53:43.51427+00:00
-- url     : https://prove2.me/theorems/80d52751-6980-4695-9c57-e7c1b032ffc9
-- title:
--   Lemma 8: the composed quantum correction has zero right derivative
-- statement:
--   Let $e\ge2$ be an integer, $c\ge0$ a real constant and $r>1$. With $h$ the binary entropy in bits, define
--   $$
--   f_1(e,\eta)=\frac\eta2\log_2(e-1)+\eta\log_2e+h(\eta/2)+(1+\eta/2)h\!\left(\frac\eta{2+\eta}\right).
--   $$
--   The composition has right derivative zero at the noise-free point:
--   $$
--   \left.\frac{d}{dp^+}f_1(e,cp^r)\right|_{p=0}=0.
--   $$
--   Only a physical right neighborhood of zero is relevant. The case $c=0$ is included as the constant-zero composition. The result explains the tangency of the capacity correction to coherent information.
-- source:
--   Quantum and private capacities of low-noise channels, arXiv:1705.04335v3, PDF p. 9, Lemma 8: the composed quantum correction has zero right derivative

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P50

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Intakethird100.P50

variable {A B E F : Type}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F]

open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel maximumCoherentInformation
    dilationPower idealJoint)

open QAlgorithms.Papers.Independent.Information100.P80 (log2)

open QAlgorithms.Papers.Independent.Information100.P69 (diamond choi)

open QAlgorithms.Papers.Independent.Support50.P07 (fullTracePrivateCapacity)

open QAlgorithms.Papers.Independent.Frontier18.P17 (clock)

/-- Lemma 8, PDF p.9: right derivative on physical p≥0, including c=0.
Choi rank e≥2 is the domain of the displayed entropy correction. -/
theorem quantumCorrection_zero_rightDerivative (e : ℕ) (he : 2 ≤ e)
    (c r : ℝ) (hc : 0 ≤ c) (hr : 1 < r) :
    HasDerivWithinAt (fun p : ℝ => quantumCorrection e (c * p ^ r)) 0 (Set.Ici 0) 0 := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P50

end
