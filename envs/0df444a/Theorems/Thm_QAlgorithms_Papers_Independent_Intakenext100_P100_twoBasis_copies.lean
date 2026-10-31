-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P100_twoBasis_copies
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P100.twoBasis_copies
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T23:17:27.80866+00:00
-- url     : https://prove2.me/theorems/3c6c12e9-0e59-4655-9927-cc3f73fb013a
-- title:
--   Additivity for copies of the two-basis locking state
-- statement:
--   Let $\rho$ be the normalized two-basis locking state above, for $d\ge1$ and two mutually unbiased unitary bases. For every integer $m\ge0$, group all Alice registers together and all Bob registers together in the independent tensor power. Then
--   $$I_c(\rho^{\otimes m})=m I_c(\rho).$$
--   Here $I_c$ optimizes all finite independent local POVMs, including joint measurements across each party's copies, and the empty tensor power is the scalar product state. This assertion applies to the explicit family, rather than to arbitrary bipartite states.
-- source:
--   Locking classical correlation in quantum states, arXiv:quant-ph/0303088v1, PDF p. 3, Following Eq. (7)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P100

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P100

open QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.3, following Eq.(7): additivity for this explicit two-basis family
only, including the empty tensor product m=0. -/
theorem twoBasis_copies (d : ℕ) (hd : 0 < d)
    (U : Fin 2 → Matrix.unitaryGroup (Fin d) ℂ) (hU : IsUnbiasedFamily U) (m : ℕ) :
    IsDensityMatrix (lockingCopies U m) ∧
    lockingMeasuredInformation (lockingCopies U m) =
      (m : ℝ) * lockingMeasuredInformation (lockingState U) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P100

end
