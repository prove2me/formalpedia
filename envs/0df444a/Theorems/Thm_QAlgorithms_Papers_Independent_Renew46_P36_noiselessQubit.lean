-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P36_noiselessQubit
-- name    : QAlgorithms.Papers.Independent.Renew46.P36.noiselessQubit
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T22:06:33.806376+00:00
-- url     : https://prove2.me/theorems/312c7871-7a52-43d9-8167-21701aaee832
-- title:
--   §2: optimal time-sharing for a noiseless qubit
-- statement:
--   Let $\mathrm{id}_2$ be the identity quantum channel on a two-dimensional complex register. For each unassisted scenario $s\in\{\mathrm{Ia},\mathrm{Ib},\mathrm{II}\}$, let $S_s$ denote nonnegative asymptotically achievable rates in bits and qubits per use, with per-message classical error and squared-fidelity quantum error tending to zero. Then
--
--   $$
--   S_s(\mathrm{id}_2)=\{(r,R)\in\mathbb R^2:r\geq0,\ R\geq0,\ r+R\leq1\}.
--   $$
--
--   Thus time-sharing completely determines the simultaneous region of a noiseless qubit, including both axes.
-- source:
--   The capacity of a quantum channel for simultaneous transmission of classical and quantum information, arXiv:quant-ph/0311131v3, PDF p. 5, §2: optimal time-sharing for a noiseless qubit

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P36

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Renew46.P36

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble canonicalPurification)

open QAlgorithms.Papers.Independent.Dependency50.P07 (Typical)

open QAlgorithms.Papers.Independent.Information100.P27 (qubitDephasing)

open QAlgorithms.Papers.Independent.Dependency50.P41 (maximallyEntangled)

open QAlgorithms.Papers.Independent.Claimed50.P20 (DynamicPureEnsemble pureOutputs cqHolevoBits conditionalCoherent)

open QAlgorithms.Papers.Independent.Information100.P67
  (IsDegradable receiverChannel complementaryChannel maximumCoherentInformation squaredFidelity)

open QAlgorithms.Papers.Independent.Information100.P76 (maximallyMixed)

open QAlgorithms.Papers.Independent.Information100.P80 (quantumCapacity)

open QAlgorithms.Papers.Independent.Next46.P40
  (dephasingIsometry generalizedDephasing diagonalPart)

variable {A B E A1 A2 E1 E2 : Type}

variable [Fintype A] [Fintype B] [Fintype E]

variable [Fintype A1] [Fintype A2] [Fintype E1] [Fintype E2]

/-- Section 2, PDF p.5: exact simultaneous region of a noiseless qubit. -/
theorem noiselessQubit (s : Scenario) :
    simultaneousOperationalRegion s (fun X : Matrix (Fin 2) (Fin 2) ℂ => X) =
      {v : ℝ × ℝ | 0 ≤ v.1 ∧ 0 ≤ v.2 ∧ v.1 + v.2 ≤ 1} := by sorry

end QAlgorithms.Papers.Independent.Renew46.P36

end
