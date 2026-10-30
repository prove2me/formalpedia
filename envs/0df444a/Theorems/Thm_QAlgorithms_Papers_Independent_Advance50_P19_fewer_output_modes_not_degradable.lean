-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P19_fewer_output_modes_not_degradable
-- name    : QAlgorithms.Papers.Independent.Advance50.P19.fewer_output_modes_not_degradable
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T11:56:03.50439+00:00
-- url     : https://prove2.me/theorems/1b2f23e0-c2c7-4861-8f25-e13ae3a41447
-- title:
--   Fewer output modes preclude degradability
-- statement:
--   Let $T$ be a fermionic Gaussian CPTP channel from $n$ modes to $m$ modes, with real covariance parameters $A\in\mathbb R^{2m\times2n}$ and skew-symmetric $B\in\mathbb R^{2m\times2m}$. Fix the canonical Gaussian action on the entire CAR operator algebra. If $m<n$, then
--
--   $$T\text{ is not degradable}.$$
--
--   Thus no arbitrary CPTP map from the receiver output can reproduce a pure-dilation complementary output on every input. This is the fewer-output-modes assertion, retained separately from the source's stronger singular-matrix claim.
-- source:
--   Degradability of Fermionic Gaussian Channels, arXiv:1604.01954v2, PDF p. 5, Unnumbered n to m<n obstruction

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P19

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Advance50.P19

open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel)

open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)

open QAlgorithms.Papers.Independent.Information100.P80 (quantumCapacity)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.5,7: fewer output than input modes precludes every CPTP
degrading map. The source's implication from arbitrary singular A has a gap;
that stronger, false claim is deferred, and is not assumed here. -/
theorem fewer_output_modes_not_degradable {n m : ℕ} (s : CARSystem n)
    (t : CARSystem m) (T : Superop (Qubits n) (Qubits m))
    (A : Matrix (Major m) (Major n) ℝ) (B : Matrix (Major m) (Major m) ℝ)
    (hT : IsFGC s t T A B) (hmn : m < n) :
    ¬ ChannelDegradable T := by sorry

end QAlgorithms.Papers.Independent.Advance50.P19

end
