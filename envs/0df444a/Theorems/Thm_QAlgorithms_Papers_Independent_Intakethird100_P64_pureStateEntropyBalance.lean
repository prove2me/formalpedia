-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P64_pureStateEntropyBalance
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P64.pureStateEntropyBalance
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:34:26.772364+00:00
-- url     : https://prove2.me/theorems/24fc94f3-7e3b-4ff9-a63c-892423e0f821
-- title:
--   Pure tripartite entropy balance
-- statement:
--   Let $|\psi\rangle$ be a unit pure state on finite nonzero registers $R,A,B$. For each subsystem $X$, let $H(X)_\psi$ be the von Neumann entropy in bits of its reduced density matrix, and put $I(X;Y)_\psi=H(X)_\psi+H(Y)_\psi-H(XY)_\psi$. Then
--
--   $$
--   H(A)_\psi=\tfrac12 I(R;A)_\psi+\tfrac12 I(A;B)_\psi.
--   $$
--
--   This identity determines how Alice's residual entropy divides between the two mutual-information rates in the feedback father calculation. Complementary entropy equalities are consequences of purity, not additional hypotheses.
-- source:
--   A triangle of dualities: reversibly decomposable quantum channels, source-channel duality, and time reversal, arXiv:quant-ph/0505138v1, PDF p. 2, Equation (8): pure-state entropy balance

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P64

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P64

open QAlgorithms

open QAlgorithms.Papers.Independent.Gap48.P20
  (Copies redistributionMarginal subsystemEntropy forwardApply)

open QAlgorithms.Papers.Independent.Dependency50.P48 (densityPower)

open scoped Matrix ComplexConjugate

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.2, (8): the entropy balance of every normalized finite tripartite pure
state. Purity and normalization are provided by the vector and IsState, rather
than by assuming complementary entropy equalities. -/
theorem pureStateEntropyBalance {R A B : Type}
    [Fintype R] [Fintype A] [Fintype B] [Nonempty R] [Nonempty A] [Nonempty B]
    (psi : EuclideanSpace ℂ (R × (A × B))) (hpsi : IsState psi) :
    feedbackEntropyA psi = (1 / 2 : ℝ) * mutualRA psi + (1 / 2 : ℝ) * mutualAB psi := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P64

end
