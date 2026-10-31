-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P65_rootAdmissibleAdmissible
-- name    : QAlgorithms.Papers.Independent.Intake100.P65.rootAdmissibleAdmissible
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:19:53.646238+00:00
-- url     : https://prove2.me/theorems/f60babd2-658d-4407-ac86-3d3f8b33c624
-- title:
--   Root admissibility implies ordinary admissibility
-- statement:
--   Let $R$ be a commutative unital ring with $2$ invertible, $r\ge1$, and $u\in R^r$. If $\Omega=(\omega_a)_{a\ge0}$ is $u$-admissible, then, for every $a\ge0$,
--
--   $$2\omega_{2a+1}=-\omega_{2a}+\sum_{b=1}^{2a+1}(-1)^{b-1}\omega_{b-1}\omega_{2a+1-b}.$$
--
--   Thus $\Omega$ is admissible in Definition 2.10. This permits use of the affine admissibility results at all root-admissible parameters.
-- source:
--   Cyclotomic Nazarov-Wenzl algebras, arXiv:math/0506467v5, PDF p. 16, Corollary 3.9

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P65

noncomputable section

open scoped BigOperators TensorProduct

open QAlgorithms.Papers.Independent.Renew46.P16

open QAlgorithms.Papers.Independent.Support21.P08 (IrreducibleRepresentation)

open QAlgorithms.Papers.Independent.Support21.P12

open QAlgorithms.Papers.Independent.Support21.P14 (BrauerPairing oddPairingCount)

namespace QAlgorithms.Papers.Independent.Intake100.P65

universe u v

/-- Corollary 3.9, PDF p.16: u-admissibility implies ordinary admissibility
without a field, distinctness, or nonzero-root restriction. -/
theorem rootAdmissibleAdmissible (R : Type u) [CommRing R] [Invertible (2 : R)]
    (omega : ℕ → R) (r : ℕ) (hr : 1 ≤ r) (roots : Fin r → R)
    (ha : RootAdmissible omega roots) : OmegaAdmissible omega := by sorry

end QAlgorithms.Papers.Independent.Intake100.P65

end
