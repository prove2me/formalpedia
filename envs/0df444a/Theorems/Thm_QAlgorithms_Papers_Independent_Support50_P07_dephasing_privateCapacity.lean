-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P07_dephasing_privateCapacity
-- name    : QAlgorithms.Papers.Independent.Support50.P07.dephasing_privateCapacity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T18:54:39.407701+00:00
-- url     : https://prove2.me/theorems/2ee035a1-b2b3-44ad-bf52-e3ce570d42a5
-- title:
--   Section IV.A and reference note [28]: dephasing private capacity
-- statement:
--   Choose any Pauli axis $P\in\{X,Y,Z\}$ and $p\in[0,1]$. For the receiver map $\mathcal N(\rho)=(1-p)\rho+pP\rho P^\dagger$, with any full isometric dilation,
--
--   $$C_p(\mathcal N)=1-H(p).$$
--
--   The private capacity uses the full trace-norm operational criterion above, arbitrary mixed block inputs, uniform messages and normalized POVMs; $H$ is binary entropy in bits. All parameter endpoints and all three Pauli axes are included.
-- source:
--   The private classical capacity with a symmetric side channel and its application to quantum cryptography, arXiv:0705.3838v1, PDF p. 7, Section IV.A and reference note [28]: dephasing private capacity

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P07

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Support50.P07

open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel IsDegradable IsAntidegradable
    dilationPower idealJoint maximumCoherentInformation)

open QAlgorithms.Papers.Independent.Claimed50.P24 (productDilation)

open QAlgorithms.Papers.Independent.Dependency50.P19 (mutualInformation)

variable {A B E C D F : Type}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype E] [DecidableEq E] [Fintype C] [DecidableEq C]

variable [Fintype D] [DecidableEq D] [Fintype F] [DecidableEq F]

/-- PDF pp.6–7 and note [28], p.8: general channel private capacity, allowing
arbitrary mixed and entangled signal states, equals the dephasing formula.
All three Pauli axes are included, as in IV.A and the proof of Theorem 12. -/
theorem dephasing_privateCapacity [Nonempty E]
    (U : Matrix (Fin 2 × E) (Fin 2) ℂ)
    (hU : IsIsometry U) (axis : Fin 3) (p : ℝ) (hp : p ∈ Set.Icc 0 1)
    (hmap : receiverChannel U =
      qubitPauliProbabilityChannel (fun i => if i = axis then p else 0)) :
    fullTracePrivateCapacity U = 1 - binEntropy2 p := by sorry

end QAlgorithms.Papers.Independent.Support50.P07

end
