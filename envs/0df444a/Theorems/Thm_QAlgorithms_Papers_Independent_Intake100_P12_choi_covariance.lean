-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P12_choi_covariance
-- name    : QAlgorithms.Papers.Independent.Intake100.P12.choi_covariance
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:59:07.762175+00:00
-- url     : https://prove2.me/theorems/25cc8cfd-375e-46fb-b760-f1f44c4fa6b2
-- title:
--   Output-first Choi covariance
-- statement:
--   Let $d\ge1$ and $U,A,B\in U(d)$, in the fixed computational bases. Write $C(V)$ for the unnormalized, output-first Choi matrix of the channel $X\mapsto VXV^\dagger$. Then
--
--   $$ (A\otimes B)C(U)(A^\dagger\otimes B^\dagger)=C(AUB^{\mathsf T}). $$
--
--   The transpose on $B$ records the input leg convention of the Choi representation.
-- source:
--   Probabilistic exact universal quantum circuits for transforming unitary operations, arXiv:1909.01366v2, PDF p. 2, II A, Eq. (3)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P12

noncomputable section

open QAlgorithms

open scoped Matrix ComplexConjugate ComplexOrder Kronecker

namespace QAlgorithms.Papers.Independent.Intake100.P12

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Dependency50.P26 (ChannelChoi)

/-- PDF p.2, Eq. (3): unitary-channel Choi covariance, with B transposed. -/
theorem choi_covariance {d : ℕ} (hd : 0 < d)
    (U A B : Matrix.unitaryGroup (Fin d) ℂ) :
    ((A : Op (Fin d)) ⊗ₖ (B : Op (Fin d))) * gateChoi (U : Op (Fin d)) *
      (((A : Op (Fin d)) ⊗ₖ (B : Op (Fin d)))ᴴ) =
    gateChoi ((A : Op (Fin d)) * (U : Op (Fin d)) * (B : Op (Fin d)).transpose) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P12

end
