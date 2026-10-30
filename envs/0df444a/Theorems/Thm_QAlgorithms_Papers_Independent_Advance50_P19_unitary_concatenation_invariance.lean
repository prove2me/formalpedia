-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P19_unitary_concatenation_invariance
-- name    : QAlgorithms.Papers.Independent.Advance50.P19.unitary_concatenation_invariance
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:00:10.23605+00:00
-- url     : https://prove2.me/theorems/912fc441-1f47-4c53-89a6-9a7779c4c8c6
-- title:
--   Unitary invariance of degradability and antidegradability
-- statement:
--   Let $T:\mathcal B(H_A)\to\mathcal B(H_B)$ be a quantum channel on nonzero finite-dimensional spaces. For arbitrary input and output unitaries $U_1,U_2$, define $T'(X)=U_2T(U_1XU_1^\dagger)U_2^\dagger$. Then both equivalences hold:
--
--   $$T\text{ degradable}\iff T'\text{ degradable},\qquad T\text{ antidegradable}\iff T'\text{ antidegradable}.$$
--
--   This invariance concerns general CPTP channels and general unitaries, and applies in particular when choosing Gaussian standard-form coordinates.
-- source:
--   Degradability of Fermionic Gaussian Channels, arXiv:1604.01954v2, PDF p. 8, Lemma S6

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P19

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Advance50.P19

open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel)

open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)

open QAlgorithms.Papers.Independent.Information100.P80 (quantumCapacity)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.8, Lemma S6: BOTH degradability and antidegradability are
invariant under arbitrary unitary input/output channels, not just Gaussian ones. -/
theorem unitary_concatenation_invariance {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Nonempty A] [Nonempty B] (T : Superop A B) (hT : IsChannel T)
    (U1 : Matrix.unitaryGroup A ℂ) (U2 : Matrix.unitaryGroup B ℂ) :
    let transformed : Superop A B := fun X =>
      (U2 : Matrix B B ℂ) *
        T ((U1 : Matrix A A ℂ) * X * (U1 : Matrix A A ℂ).conjTranspose) *
        (U2 : Matrix B B ℂ).conjTranspose
    (ChannelDegradable T ↔ ChannelDegradable transformed) ∧
      (ChannelAntidegradable T ↔ ChannelAntidegradable transformed) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P19

end
