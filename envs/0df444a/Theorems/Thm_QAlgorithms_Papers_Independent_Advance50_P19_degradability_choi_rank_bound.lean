-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P19_degradability_choi_rank_bound
-- name    : QAlgorithms.Papers.Independent.Advance50.P19.degradability_choi_rank_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:03:30.632751+00:00
-- url     : https://prove2.me/theorems/23a99018-7fe7-4fd0-9053-1679668a02f4
-- title:
--   Degradable equal-mode Gaussian channels have small Choi rank
-- statement:
--   Let $T$ be an $n\to n$ fermionic Gaussian CPTP channel. If $T$ is degradable by an arbitrary CPTP map, then
--
--   $$\operatorname{rank}J(T)\le2^n,\qquad r(T)\le n,$$
--
--   where $J(T)$ is the actual normalized ordinary Choi density and $r(T)=\log_2\operatorname{rank}J(T)$ is its rank in fermionic modes. Neither invertibility of $A$ nor a perfect-mode reduction is an additional hypothesis. This bounds the minimal pure-environment size for equal input/output mode counts.
-- source:
--   Degradability of Fermionic Gaussian Channels, arXiv:1604.01954v2, PDF p. 9, Lemma S10

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P19

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Advance50.P19

open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel)

open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)

open QAlgorithms.Papers.Independent.Information100.P80 (quantumCapacity)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.9-10, Lemma S10: ordinary Choi rank at most 2^n, equivalently
at most n MODES for an FGC. No invertibility or perfect-mode reduction is
assumed: both are proof issues in the source. No extension to m>n is claimed. -/
theorem degradability_choi_rank_bound {n : ℕ} (s t : CARSystem n)
    (T : Superop (Qubits n) (Qubits n)) (A B : Matrix (Major n) (Major n) ℝ)
    (hT : IsFGC s t T A B) (hdeg : ChannelDegradable T) :
    Matrix.rank (normalizedChoiDensity T) ≤ 2 ^ n ∧ choiModeRank T ≤ n := by sorry

end QAlgorithms.Papers.Independent.Advance50.P19

end
