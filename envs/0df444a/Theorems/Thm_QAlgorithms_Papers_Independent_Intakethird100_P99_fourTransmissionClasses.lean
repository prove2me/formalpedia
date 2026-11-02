-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P99_fourTransmissionClasses
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P99.fourTransmissionClasses
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T10:16:49.121527+00:00
-- url     : https://prove2.me/theorems/8c8b31c8-475d-4895-8acf-4d43b6149a59
-- title:
--   Four disjoint transmission-capability classes
-- statement:
--   For a two-qubit unitary $U$, let $\beta$ be an actual interaction-content witness: $U$ is locally equivalent, up to global phase, to $U_\beta=\exp[-i\sum_{k=1}^3\beta_k\sigma_k\otimes\sigma_k]$, where $\sigma_1,\sigma_2,\sigma_3$ are the Pauli matrices $X,Y,Z$ and $\pi/4\ge\beta_1\ge\beta_2\ge|\beta_3|$. Transmission means one use of the gate with normalized pure product inputs, without ancillas or prior shared entanglement. Encoding and decoding axes are free local choices fixed before the unknown input. Classical messages are encoded in orthogonal states and decoded with certainty; qubit transmission preserves every superposition with the same encoding and recovery. In simultaneous tasks, a receiver may choose its local decoder according to its own sent classical bit. Every gate belongs to exactly one of the following four operational profiles, equivalent to the indicated disjoint chamber stratum:
--
--   $$\begin{array}{c|c} \text{stratum}&\text{perfect transmission tasks}\\ \beta_1<\pi/4&\text{none}\\ \beta_1=\pi/4,\ \beta_2<\pi/4&\text{one cbit only}\\ \beta_1=\beta_2=\pi/4,\ |\beta_3|<\pi/4&\text{two cbits; qubit plus reverse cbit; no two qubits}\\ \beta_1=\beta_2=|\beta_3|=\pi/4&\text{all tasks (SWAP class)} \end{array}$$
--
--   One-way tasks in this table are possible in either chosen direction. The empty profile excludes a perfect full bit in one use and does not assert zero Shannon capacity.
-- source:
--   Characterization of non-local gates, arXiv:quant-ph/0205100v3, PDF p. 12, IV.C: four transmission-capability classes

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P99

namespace QAlgorithms.Papers.Independent.Intakethird100.P99

open scoped Matrix Kronecker NNReal ENNReal

open QAlgorithms.Papers.Independent.Information100.P10 (pauli)

open QAlgorithms.Papers.Independent.Information100.P32 (evolution)

noncomputable section

/-- PDF p.12, IV.C: precisely four disjoint operational classes. Endpoints of lower
strata are excluded, and both signs of SWAP's last coefficient are included. -/
theorem fourTransmissionClasses (U : TwoMatrix) (b : Triple) (hU : HasContent U b) :
    (∀ k : Fin 4, ChamberClass b k ↔ TransmissionProfile U k) ∧
      ∃! k : Fin 4, TransmissionProfile U k := by sorry

end

end QAlgorithms.Papers.Independent.Intakethird100.P99
