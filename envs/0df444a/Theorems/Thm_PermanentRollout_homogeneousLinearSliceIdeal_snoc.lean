-- Prove2me | Theorems.Thm_PermanentRollout_homogeneousLinearSliceIdeal_snoc
-- name    : PermanentRollout.homogeneousLinearSliceIdeal_snoc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:34.673665+00:00
-- url     : https://prove2.me/theorems/5e8090ea-376a-4bf0-af3a-b8520af8b681
-- title:
--   PermanentRollout.homogeneousLinearSliceIdeal_snoc
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | Permanent | external Lean 4.33.1 validation; bundle SHA256 8a836240c656ca1eb46e7ecec147014a94283bee53230c4428d90fa24026d93c

import Mathlib
import Definitions.Def_Permanent
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped LinearAlgebra.Projectivization
attribute [local instance] MvPolynomial.gradedAlgebra

theorem PermanentRollout.homogeneousLinearSliceIdeal_snoc {t n : ℕ}
    (I : Ideal (MvPolynomial (Fin t) ℂ))
    (c : Fin n → Fin t → ℂ) (x : Fin t → ℂ) :
    homogeneousLinearSliceIdeal I (Fin.snoc c x) =
      homogeneousLinearSliceIdeal I c ⊔
        Ideal.span
          ({permanentRolloutLinearCoordinateCombination t x} :
            Set (MvPolynomial (Fin t) ℂ)) := by sorry
