-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P99_cbitCapability_iff
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P99.cbitCapability_iff
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T10:12:54.179651+00:00
-- url     : https://prove2.me/theorems/50a24273-27c8-4962-a854-c3a8e1dbd661
-- title:
--   Perfect one-cbit transmission criterion
-- statement:
--   For a two-qubit unitary $U$, let $\beta$ be an actual interaction-content witness: $U$ is locally equivalent, up to global phase, to $U_\beta=\exp[-i\sum_{k=1}^3\beta_k\sigma_k\otimes\sigma_k]$, where $\sigma_1,\sigma_2,\sigma_3$ are the Pauli matrices $X,Y,Z$ and $\pi/4\ge\beta_1\ge\beta_2\ge|\beta_3|$. Transmission means one use of the gate with normalized pure product inputs, without ancillas or prior shared entanglement. Encoding and decoding axes are free local choices fixed before the unknown input. Classical messages are encoded in orthogonal states and decoded with certainty; qubit transmission preserves every superposition with the same encoding and recovery. In simultaneous tasks, a receiver may choose its local decoder according to its own sent classical bit. The receiving party may choose one fixed pure preparation suited to the gate; it need not work for every preparation. Then
--
--   $$U\text{ can send one perfect cbit }A\to B\quad\Longleftrightarrow\quad\beta_1=\pi/4.$$
--
--   The same equivalence holds with $A,B$ exchanged. This identifies the first transmission threshold in the canonical chamber.
-- source:
--   Characterization of non-local gates, arXiv:quant-ph/0205100v3, PDF p. 9, IV.B.1: exact criterion for one classical bit

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P99

namespace QAlgorithms.Papers.Independent.Intakethird100.P99

open scoped Matrix Kronecker NNReal ENNReal

open QAlgorithms.Papers.Independent.Information100.P10 (pauli)

open QAlgorithms.Papers.Independent.Information100.P32 (evolution)

noncomputable section

/-- PDF pp.9–10, IV.B.1: a single perfect classical bit is possible precisely on the
first chamber face. The receiver's preparation is existential, not universal. -/
theorem cbitCapability_iff (U : TwoMatrix) (b : Triple) (hU : HasContent U b) :
    (CanCbit U ↔ b 0 = Real.pi / 4) ∧
      (CanCbit (reverseParties U) ↔ b 0 = Real.pi / 4) := by sorry

end

end QAlgorithms.Papers.Independent.Intakethird100.P99
