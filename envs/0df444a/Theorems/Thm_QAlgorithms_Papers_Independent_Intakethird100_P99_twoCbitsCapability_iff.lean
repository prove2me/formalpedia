-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P99_twoCbitsCapability_iff
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P99.twoCbitsCapability_iff
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T10:13:43.147739+00:00
-- url     : https://prove2.me/theorems/28d27162-3f1b-438c-8889-04ffdf0d7ce9
-- title:
--   Perfect bidirectional-cbit transmission criterion
-- statement:
--   For a two-qubit unitary $U$, let $\beta$ be an actual interaction-content witness: $U$ is locally equivalent, up to global phase, to $U_\beta=\exp[-i\sum_{k=1}^3\beta_k\sigma_k\otimes\sigma_k]$, where $\sigma_1,\sigma_2,\sigma_3$ are the Pauli matrices $X,Y,Z$ and $\pi/4\ge\beta_1\ge\beta_2\ge|\beta_3|$. Transmission means one use of the gate with normalized pure product inputs, without ancillas or prior shared entanglement. Encoding and decoding axes are free local choices fixed before the unknown input. Classical messages are encoded in orthogonal states and decoded with certainty; qubit transmission preserves every superposition with the same encoding and recovery. In simultaneous tasks, a receiver may choose its local decoder according to its own sent classical bit. Then
--
--   $$U\text{ can send one perfect cbit each way simultaneously}\quad\Longleftrightarrow\quad\beta_1=\beta_2=\pi/4.$$
--
--   The third coordinate is unrestricted within the canonical chamber, $|\beta_3|\le\pi/4$. The two input encodings are chosen before either bit; each receiver may use the sent bit to select a decoding observable.
-- source:
--   Characterization of non-local gates, arXiv:quant-ph/0205100v3, PDF p. 10, IV.B.2: gates enabling one classical bit each way

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P99

namespace QAlgorithms.Papers.Independent.Intakethird100.P99

open scoped Matrix Kronecker NNReal ENNReal

open QAlgorithms.Papers.Independent.Information100.P10 (pauli)

open QAlgorithms.Papers.Independent.Information100.P32 (evolution)

noncomputable section

/-- PDF pp.10–11, IV.B.2, (16)–(19): simultaneous perfect cbits are possible precisely
on the edge with the first two coordinates pi/4. Decoding may depend on the sent bit. -/
theorem twoCbitsCapability_iff (U : TwoMatrix) (b : Triple) (hU : HasContent U b) :
    CanTwoCbits U ↔ b 0 = Real.pi / 4 ∧ b 1 = Real.pi / 4 := by sorry

end

end QAlgorithms.Papers.Independent.Intakethird100.P99
